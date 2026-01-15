# ACL2 Jupyter Kernel Implementation Specification

## Executive Summary

Build a native ACL2 Jupyter kernel that implements the ipykernel 7 protocol (Jupyter Kernel Protocol v5.3) directly in Common Lisp (SBCL/CCL), without Python wrappers. The kernel communicates with Jupyter Server via ZeroMQ sockets using either TCP or Unix domain sockets (IPC), with HMAC-SHA256 message signing.

**Target:** Fully functional REPL kernel with execute, heartbeat, and kernel_info support. Phase 2 adds completion, inspection, and interrupt handling.

---

## 1. Architecture Overview

### 1.1 Component Stack

```
acl2-kernel/
├── kernel-main.lisp              # Entry point, event loop orchestrator
├── connection-file-parser.lisp    # Parse JSON connection file
├── zmq-socket-manager.lisp        # ZeroMQ socket lifecycle
├── message-envelope.lisp          # Message serialization, HMAC signing
├── kernel-state.lisp              # Global state (execution_count, session, etc.)
├── request-dispatcher.lisp        # Route messages to handlers
├── request-handlers.lisp          # kernel_info, execute, shutdown handlers
├── heartbeat-responder.lisp       # Background heartbeat echo
├── output-capture.lisp            # Redirect stdout/stderr during execution
├── acl2-eval.lisp                 # Hook into ACL2 evaluation
├── util.lisp                      # JSON, UUID, HMAC utilities
├── kernel.json                    # Jupyter kernel specification
└── tests/                         # Unit and integration tests
```

### 1.2 Execution Flow

```
1. Jupyter Server invokes kernel via kernel.json argv
   $ sbcl --script kernel-main.lisp -f /path/to/connection_file.json

2. kernel-main.lisp:
   a) Parse connection file → extract transport, IP, ports, HMAC key
   b) Store globals: *session-id*, *hmac-key*, *execution-count*
   c) Initialize 5 ZeroMQ sockets (shell, control, iopub, stdin, heartbeat)
   d) Start background thread for heartbeat responder
   e) Enter main event loop

3. Event Loop:
   a) Poll shell, control, stdin sockets (non-blocking, ~100ms timeout)
   b) On message arrival:
      - Deserialize multipart message
      - Verify HMAC signature
      - Extract msg_type from header
      - Dispatch to appropriate handler
   c) Handler processes request, publishes IOPub messages, sends reply
   d) Continue until shutdown_request or SIGTERM

4. Kernel State Persists:
   - ACL2 package/namespace remains loaded
   - *execution-count* increments per execute_request
   - Command history accumulated for history_request
```

### 1.3 Socket Topology (ZeroMQ)

| Channel    | Socket Type | Direction      | Transport   | Purpose                                    |
|------------|-------------|----------------|-------------|--------------------------------------------|
| shell      | DEALER      | Bidirectional  | TCP/IPC     | execute, complete, inspect, history        |
| control    | DEALER      | Bidirectional  | TCP/IPC     | interrupt, shutdown (higher priority)      |
| iopub      | PUB         | Outbound only  | TCP/IPC     | status, stream, result, error, display     |
| stdin      | ROUTER      | Bidirectional  | TCP/IPC     | input_request/input_reply (future)         |
| heartbeat  | REP         | Bidirectional  | TCP/IPC     | Echo (keepalive)                           |

**Transport Modes:**
- **TCP:** `tcp://127.0.0.1:port` (default, works over network)
- **IPC:** `ipc:///run/user/1000/jupyter-kernel-shell.sock` (Unix domain sockets, preferred for local)

---

## 2. Connection File Format & Parsing

### 2.1 Connection File (TCP Example)

```json
{
  "transport": "tcp",
  "ip": "127.0.0.1",
  "shell_port": 57503,
  "control_port": 50160,
  "iopub_port": 40885,
  "stdin_port": 52597,
  "hb_port": 42540,
  "key": "a0436f6c-1916-498b-8eb9-e81ab9368e84",
  "signature_scheme": "hmac-sha256",
  "kernel_name": "acl2"
}
```

### 2.2 Connection File (IPC Example)

```json
{
  "transport": "ipc",
  "kernel_name": "acl2",
  "signature_scheme": "hmac-sha256",
  "key": "a0436f6c-1916-498b-8eb9-e81ab9368e84",
  "shell_port": "/run/user/1000/jupyter-kernel-shell.sock",
  "control_port": "/run/user/1000/jupyter-kernel-control.sock",
  "iopub_port": "/run/user/1000/jupyter-kernel-iopub.sock",
  "stdin_port": "/run/user/1000/jupyter-kernel-stdin.sock",
  "hb_port": "/run/user/1000/jupyter-kernel-hb.sock"
}
```

### 2.3 Parsing Algorithm

```lisp
(defun parse-connection-file (path)
  "Parse JSON connection file into alist.
   Return: ((transport . tcp) (ip . 127.0.0.1) (shell-port . 57503) ...)"
  ;; 1. Read file as string
  ;; 2. JSON decode using existing JSON parser
  ;; 3. Extract keys: transport, ip|shell_port|iopub_port|etc., key, signature_scheme
  ;; 4. Build alist, validate required fields
  ;; 5. Return parsed data
  )
```

**Validation:**
- `:transport` ∈ {"tcp", "ipc"}
- `:key` is non-empty string (HMAC secret, store securely)
- `:signature-scheme` = "hmac-sha256" (only supported scheme)
- Port numbers (TCP) > 1024 or IPC paths valid filesystem paths
- No exceptions; graceful error if missing fields

---

## 3. Jupyter Kernel Protocol (v5.3)

### 3.1 Message Envelope Structure

**Every message** follows this JSON structure:

```json
{
  "header": {
    "msg_id": "uuid-v4-string",
    "msg_type": "execute_request",
    "session": "session-uuid",
    "date": "2026-01-15T13:32:00.000000Z",
    "version": "5.3"
  },
  "parent_header": { },
  "metadata": { },
  "content": {
    // Type-specific payload (varies per msg_type)
  }
}
```

### 3.2 ZeroMQ Multipart Message Format

Messages are sent as **multipart** on ZeroMQ sockets:

```
[0] = JSON-encoded header
[1] = JSON-encoded parent_header
[2] = JSON-encoded metadata
[3] = JSON-encoded content
[4] = HMAC-SHA256 signature (hex string)
```

**Note:** Some sockets include routing frames (ROUTER/DEALER add frames); strip these before parsing.

### 3.3 HMAC-SHA256 Signing

**Signature Computation:**
```
signature = HMAC-SHA256(
  key = connection_file["key"],
  msg = json(header) + json(parent_header) + json(metadata) + json(content)
)
result = hex-encode(signature)
```

**Verification:**
1. Receive multipart message
2. Extract header, parent, metadata, content, signature (multipart[0:5])
3. Concatenate JSON of first 4 parts
4. Compute expected signature with stored key
5. Constant-time compare with received signature
6. **Discard if mismatch** (security: prevent tampered commands)

**Signing Outgoing Messages:**
- Kernel constructs envelope (header, parent, metadata, content)
- Computes signature as above
- Sends as multipart with signature appended

### 3.4 Message Types (Phase 1)

#### 3.4.1 kernel_info_request / kernel_info_reply

**Request** (no content payload):
```json
{
  "header": { "msg_type": "kernel_info_request", ... },
  "content": {}
}
```

**Reply:**
```json
{
  "header": { "msg_type": "kernel_info_reply", "parent_header": { "msg_id": "request-id" }, ... },
  "content": {
    "protocol_version": "5.3",
    "implementation": "acl2",
    "implementation_version": "2025.01",
    "language_info": {
      "name": "acl2",
      "version": "8.7",
      "mimetype": "text/plain",
      "file_extension": ".lisp",
      "pygments_lexer": "commonlisp",
      "codemirror_mode": "commonlisp",
      "nbconvert_exporter": "script"
    },
    "banner": "ACL2 Kernel for Jupyter\nA Computational Logic for Applicative Common Lisp",
    "help_links": [
      { "text": "ACL2 Documentation", "url": "https://www.cs.utexas.edu/users/moore/acl2/" }
    ]
  }
}
```

#### 3.4.2 execute_request / execute_reply

**Request:**
```json
{
  "header": { "msg_type": "execute_request", ... },
  "content": {
    "code": "(+ 1 2)",
    "silent": false,
    "store_history": true,
    "user_expressions": {},
    "allow_stdin": true,
    "stop_on_error": true
  }
}
```

**Reply:**
```json
{
  "header": { "msg_type": "execute_reply", "parent_header": { "msg_id": "request-id" }, ... },
  "content": {
    "status": "ok",
    "execution_count": 1,
    "payload": [],
    "user_expressions": {}
  }
}
```

**Side-channel IOPub Messages** (published while executing):

1. **status: busy**
   ```json
   { "msg_type": "status", "content": { "execution_state": "busy" } }
   ```

2. **stream (stdout/stderr)**
   ```json
   { "msg_type": "stream", "content": { "name": "stdout", "text": "output\n" } }
   ```

3. **execute_result** (if not silent)
   ```json
   {
     "msg_type": "execute_result",
     "content": {
       "execution_count": 1,
       "data": { "text/plain": "3" },
       "metadata": {}
     }
   }
   ```

4. **error** (if exception)
   ```json
   {
     "msg_type": "error",
     "content": {
       "ename": "ACL2_ERROR",
       "evalue": "Undefined function: FOO",
       "traceback": [ "Error context 1", "Error context 2" ]
     }
   }
   ```

5. **status: idle**
   ```json
   { "msg_type": "status", "content": { "execution_state": "idle" } }
   ```

#### 3.4.3 Heartbeat (REP socket)

**Incoming:** Any binary message on heartbeat socket
**Outgoing:** Echo same message back immediately

No JSON parsing needed; raw echo suffices.

#### 3.4.4 shutdown_request / shutdown_reply

**Request:**
```json
{
  "header": { "msg_type": "shutdown_request", ... },
  "content": { "restart": false }
}
```

**Reply:**
```json
{
  "header": { "msg_type": "shutdown_reply", ... },
  "content": { "restart": false }
}
```

**Kernel Action:** Send reply, close all sockets, exit cleanly.

### 3.5 Message Sequencing Rules

1. **Every execute_request must:**
   - Increment `*execution-count*`
   - Publish `status: "busy"` on iopub
   - Evaluate code
   - Publish `stream` for any stdout/stderr
   - Publish `execute_result` (if not silent)
   - Send `execute_reply` on shell with `execution_count`
   - Publish `status: "idle"` on iopub

2. **parent_header correlation:**
   - All IOPub messages from an execute should have `parent_header.msg_id = original_execute_request.header.msg_id`
   - Lets frontend correlate output to cell

3. **Constant execution_count:**
   - Increments once per execute_request
   - Appears in execute_reply and execute_result
   - Used for `In[N]:`, `Out[N]:` cell numbering

---

## 4. Kernel State Management

### 4.1 Global Variables

```lisp
(defvar *session-id* nil
  "UUID from connection file, unique per kernel session")

(defvar *execution-count* 0
  "Counter incremented per execute_request")

(defvar *hmac-key* nil
  "HMAC signing key from connection file (sensitive)")

(defvar *signature-scheme* "hmac-sha256"
  "Signature algorithm (only hmac-sha256 supported)")

(defvar *message-history* nil
  "List of executed commands for history_request")

(defvar *user-namespace* nil
  "ACL2 package context, persists across executions")

(defvar *is-executing* nil
  "Flag: kernel is currently executing code (for interrupt handling)")
```

### 4.2 Execution Counter Semantics

- Starts at 0
- Increments **before** code execution
- Sent in `execute_reply.execution_count` and `execute_result.execution_count`
- Frontend displays as `In[N]:` (input) and `Out[N]:` (output)
- Persists across cell executions (never resets)

---

## 5. Request Handlers (Phase 1)

### 5.1 kernel_info_request Handler

**Location:** `request-handlers.lisp`

**Algorithm:**
```lisp
(defun handle-kernel-info-request (shell-socket envelope)
  "Respond to kernel_info_request with metadata."
  ;; 1. Extract request (no special content)
  ;; 2. Build reply envelope
  ;;    - header.msg_type = "kernel_info_reply"
  ;;    - parent_header = request.header
  ;;    - content = static metadata (language_info, protocol_version, etc.)
  ;; 3. Sign and send on shell socket
  )
```

**Response Payload (static):**
- Protocol version: "5.3"
- Implementation: "acl2"
- Implementation version: kernel version + date
- Language info: ACL2 name, version, MIME type, file extension
- Banner: Greeting message
- Help links: ACL2 documentation URL

### 5.2 execute_request Handler (Core)

**Location:** `request-handlers.lisp`

**Algorithm:**
```lisp
(defun handle-execute-request (shell-socket iopub-socket envelope)
  "Execute ACL2 code and stream results."
  ;; 1. Increment *execution-count*
  ;; 2. Extract from content: code, silent, store_history, allow_stdin
  ;; 3. Publish status "busy" on iopub with parent_header.msg_id = request.msg_id
  ;; 4. Capture stdout/stderr (redirect streams)
  ;; 5. Try:
  ;;    a) Evaluate code in ACL2 (*user-namespace*)
  ;;    b) Capture return value (convert to string)
  ;;    c) On success:
  ;;       - Stream any stdout/stderr via stream messages
  ;;       - Send execute_result (if not silent)
  ;;       - Set reply status = "ok"
  ;;    d) On error:
  ;;       - Capture exception/traceback
  ;;       - Publish error message on iopub
  ;;       - Set reply status = "error"
  ;; 6. Send execute_reply with status, execution_count
  ;; 7. Publish status "idle" on iopub
  )
```

**Implementation Details:**

**Output Capture:**
- Use Common Lisp `with-output-to-string` or similar
- Redirect `*standard-output*`, `*standard-error*` during evaluation
- Collect into buffer, parse into lines, send as separate `stream` messages

**ACL2 Evaluation:**
- Call ACL2's read-eval-print loop (or lower-level eval)
- Pass code as string
- Evaluate in `*user-namespace*` (persistent package context)
- Capture return value (last form evaluated)
- Return value format: convert to string via `format ~s`

**Error Handling:**
- Catch Common Lisp exceptions
- Extract error message and type
- Build `error` message with ename, evalue, traceback
- Continue kernel (don't exit)

**Silent Mode:**
- If `silent: true`, skip `execute_result` message
- Still send `status` and stream messages
- Used for initialization cells

### 5.3 Heartbeat Responder (Background Thread)

**Location:** `heartbeat-responder.lisp`

**Algorithm:**
```lisp
(defun heartbeat-responder (hb-socket)
  "Echo heartbeats forever (runs in background thread)."
  ;; 1. Infinite loop:
  ;;    - Receive message on hb-socket (blocking, no timeout)
  ;;    - Send same message back immediately
  ;; 2. Never exits (until kernel shutdown)
  )
```

**Implementation Notes:**
- Simplest message handler (no JSON parsing)
- Use ZeroMQ REP socket (automatic routing frame handling)
- Run in separate OS thread (use SBCL/CCL threading)
- Ensure thread is daemon (won't prevent shutdown)

---

## 6. Socket Management

### 6.1 Socket Initialization

**Location:** `zmq-socket-manager.lisp`

```lisp
(defun init-shell-socket (transport ip port)
  "Create DEALER socket for shell channel."
  ;; 1. Create ZeroMQ context (global or per-kernel)
  ;; 2. Create socket type DEALER
  ;; 3. Set socket options: ZMQ_LINGER, etc.
  ;; 4. Bind address:
  ;;    - TCP: (format nil "tcp://~a:~a" ip port)
  ;;    - IPC: port is path, use it directly
  ;; 5. Return socket handle
  )

(defun init-pub-socket (transport ip port)
  "Create PUB socket for iopub channel."
  ;; Similar to init-shell-socket but socket type = PUB
  )

(defun init-rep-socket (transport ip port)
  "Create REP socket for heartbeat."
  ;; Similar but socket type = REP
  )
```

**Socket Options:**
- `ZMQ_LINGER`: 0 (don't delay socket close)
- `ZMQ_TCP_KEEPALIVE`: 1 (if TCP)
- `ZMQ_HEARTBEAT_IVL`: 10000ms (ZeroMQ-level keepalive, optional)

### 6.2 Non-blocking Polling

**Location:** `zmq-socket-manager.lisp`

```lisp
(defun poll-sockets (socket-list timeout-ms)
  "Poll multiple sockets for readable messages (non-blocking).
   Return: List of sockets with pending messages."
  ;; 1. Build ZeroMQ poll array (ZMQ_POLLIN for each socket)
  ;; 2. Call zmq_poll with timeout_ms
  ;; 3. Filter and return sockets that have ZMQ_POLLIN set
  )
```

**Timeout Strategy:**
- Use ~100ms timeout in main event loop
- Allows responsive handling of multiple sockets
- Avoids busy-waiting

### 6.3 Graceful Shutdown

```lisp
(defun shutdown-kernel (shell iopub control stdin hb)
  "Close all sockets and exit cleanly."
  ;; 1. Publish final status "shutting_down" on iopub
  ;; 2. Close all sockets (ZMQ handles cleanup)
  ;; 3. Flush any pending messages
  ;; 4. Exit process
  )
```

---

## 7. Message Serialization & Deserialization

### 7.1 JSON Serialization

**Location:** `message-envelope.lisp`

```lisp
(defun json-serialize (obj)
  "Convert Lisp object (alist/plist) to JSON string."
  ;; Use existing JSON encoder from ACL2 Bridge or library
  ;; Handle special cases:
  ;; - Symbols → quoted strings (e.g., 'ok → "ok")
  ;; - Integers → JSON numbers
  ;; - Strings → JSON strings (escape quotes, newlines)
  ;; - Lists → JSON arrays
  ;; - Alists → JSON objects
  )

(defun json-deserialize (json-string)
  "Convert JSON string to Lisp object (alist)."
  ;; Use existing JSON decoder
  )
```

### 7.2 HMAC Computation

**Location:** `message-envelope.lisp`

```lisp
(defun compute-hmac-sha256 (message key)
  "Compute HMAC-SHA256 signature.
   Args: message (string), key (string)
   Return: hex-encoded digest (string)"
  ;; 1. Load crypto library (e.g., ironclad, uuid, or system openssl)
  ;; 2. Hash = HMAC-SHA256(key, message)
  ;; 3. Convert to hex string (lowercase)
  ;; 4. Return
  )

(defun verify-hmac-sha256 (message key signature)
  "Verify HMAC signature (constant-time comparison).
   Args: message (string), key (string), signature (hex string)
   Return: t if valid, nil otherwise"
  ;; 1. Compute expected signature
  ;; 2. Constant-time compare with received signature
  ;;    (prevent timing attacks)
  ;; 3. Return boolean
  )
```

### 7.3 UUID Generation

**Location:** `util.lisp`

```lisp
(defun uuid-v4 ()
  "Generate UUID v4 (random).
   Return: UUID as string (e.g., \"123e4567-e89b-12d3-a456-426614174000\")"
  ;; Use crypto library or UUID library
  )
```

### 7.4 ISO8601 Timestamp

**Location:** `util.lisp`

```lisp
(defun iso8601-now ()
  "Return current time in ISO8601 format.
   Return: \"2026-01-15T13:32:00.000000Z\""
  ;; Get current time, format to ISO8601 with microsecond precision
  )
```

---

## 8. Output Capture & Formatting

### 8.1 stdout/stderr Redirection

**Location:** `output-capture.lisp`

```lisp
(defun capture-output (thunk)
  "Execute thunk, capture stdout/stderr.
   Args: thunk (function with no args)
   Return: (values result-value stdout-string stderr-string)"
  ;; 1. Create string output streams for stdout, stderr
  ;; 2. Bind *standard-output*, *error-output* to these streams
  ;; 3. Call thunk, catch exceptions
  ;; 4. Retrieve accumulated strings
  ;; 5. Return (result, stdout, stderr)
  )
```

### 8.2 Result Formatting

**Location:** `request-handlers.lisp`

```lisp
(defun format-result (value)
  "Convert ACL2 result to displayable string (text/plain MIME type).
   Args: value (any Lisp object)
   Return: string"
  ;; 1. Use format ~s or ~a to convert to string
  ;; 2. Handle special cases:
  ;;    - nil → empty string
  ;;    - Long outputs → truncate or summarize
  ;; 3. Return string suitable for JSON content.data["text/plain"]
  )
```

### 8.3 Stream Chunking

**Location:** `request-handlers.lisp`

```lisp
(defun stream-output-lines (socket output parent-msg-id)
  "Publish output as stream messages (one per line).
   Args: socket (iopub), output (string), parent-msg-id (string)
   Publishes: Multiple stream messages"
  ;; 1. Split output by newlines
  ;; 2. For each line:
  ;;    - Create stream message
  ;;    - Publish on iopub
  ;; 3. Each message has parent_header.msg_id = parent-msg-id
  )
```

---

## 9. ACL2 Integration

### 9.1 Code Evaluation Entry Point

**Location:** `acl2-eval.lisp`

```lisp
(defun eval-acl2-code (code-string)
  "Evaluate ACL2 code (string).
   Args: code-string (e.g., \"(+ 1 2)\")
   Return: (values result success-flag error-message)
   
   Constraints:
   - Evaluate in *user-namespace* (persistent package)
   - Preserve state across calls (theorems, functions defined)
   - Return last form's value
   - Catch exceptions, return error info"
  
  ;; Approach 1: Use ACL2's read-eval-print loop
  ;; (acl2::read-eval-print code-string)
  
  ;; Approach 2: Manual read + eval + print
  ;; (let ((form (read-from-string code-string)))
  ;;   (eval form))
  
  ;; Handle:
  ;; - Parsing errors (unmatched parens)
  ;; - Undefined functions
  ;; - Type errors
  ;; - Infinite loops / timeouts
  )
```

### 9.2 Namespace Persistence

```lisp
(defvar *user-namespace* nil
  "ACL2 package context.
   Theorems, function definitions, and state persist here.
   Initialize at kernel startup, mutate with each execute_request.")

(defun initialize-user-namespace ()
  "Set up ACL2 package for kernel use."
  ;; Create or use existing ACL2 package
  ;; Initialize standard library
  ;; Set up any kernel-specific definitions
  )
```

### 9.3 Error Extraction

```lisp
(defun extract-error-info (error-object)
  "Convert Lisp exception to Jupyter error message.
   Args: error-object (condition)
   Return: (values ename evalue traceback)
           ename: string (e.g., \"ACL2_ERROR\")
           evalue: string (error message)
           traceback: list of strings (context)"
  ;; 1. Extract error message from condition
  ;; 2. Try to get stack trace (SBCL/CCL specific)
  ;; 3. Format nicely for notebook display
  )
```

---

## 10. Implementation Roadmap

### Phase 1: Minimum Viable Kernel (2–3 weeks)

#### Step 1: Project Setup
- [ ] Create directory structure
- [ ] Write kernel.json
- [ ] Set up build system (make, asdf, or shell script)
- [ ] Document dev environment (SBCL/CCL version, ZeroMQ bindings)
- [ ] Initialize git repo

#### Step 2: Connection File Parser
- [ ] Implement JSON deserializer (reuse from ACL2 Bridge or port)
- [ ] Parse connection file
- [ ] Extract transport, IP, ports, key, signature_scheme
- [ ] Store in globals
- [ ] Unit tests: parse TCP and IPC examples

#### Step 3: ZeroMQ Socket Manager
- [ ] Bind to ZeroMQ (low-level FFI bindings)
- [ ] Create shell DEALER socket
- [ ] Create control DEALER socket
- [ ] Create iopub PUB socket
- [ ] Create stdin ROUTER socket
- [ ] Create heartbeat REP socket
- [ ] Support both TCP and IPC transport
- [ ] Implement non-blocking poll
- [ ] Unit tests: socket creation, message send/recv

#### Step 4: Message Envelope & HMAC
- [ ] JSON serializer for envelopes
- [ ] UUID generator (v4)
- [ ] ISO8601 timestamp formatter
- [ ] HMAC-SHA256 signer (integrate crypto lib)
- [ ] Message verifier (constant-time comparison)
- [ ] Unit tests: sign/verify, tamper detection

#### Step 5: Kernel State Management
- [ ] Define global variables (*execution-count*, *session-id*, etc.)
- [ ] Initialize *user-namespace* (ACL2 package)
- [ ] Implement state reset/cleanup

#### Step 6: Heartbeat Responder
- [ ] Background thread management (SBCL/CCL threading)
- [ ] Simple echo loop on REP socket
- [ ] Keep thread alive, clean shutdown
- [ ] Integration test: send heartbeat, verify echo

#### Step 7: kernel_info_request Handler
- [ ] Deserialize incoming message
- [ ] Verify HMAC signature
- [ ] Build response envelope (static metadata)
- [ ] Sign and send reply
- [ ] Integration test: full handshake

#### Step 8: execute_request Handler (Core)
- [ ] Output capture (stdout/stderr redirection)
- [ ] Increment *execution-count*
- [ ] Publish status "busy" on iopub
- [ ] Evaluate ACL2 code (eval-acl2-code)
- [ ] Capture return value
- [ ] Stream output lines as stream messages
- [ ] Publish execute_result (if not silent)
- [ ] Error handling: publish error message, set status
- [ ] Send execute_reply
- [ ] Publish status "idle"
- [ ] Integration test: execute commands, verify output

#### Step 9: Request Dispatcher & Event Loop
- [ ] Poll shell, control, stdin sockets
- [ ] Deserialize multipart messages
- [ ] Verify HMAC signatures
- [ ] Route by msg_type to handlers
- [ ] Handle multiple concurrent requests (priority)
- [ ] Graceful shutdown (shutdown_request, SIGTERM)

#### Step 10: Integration Testing & Installation
- [ ] Create kernel.json with correct paths
- [ ] Install kernelspec: `jupyter kernelspec install ./`
- [ ] Launch kernel from JupyterLab
- [ ] Execute cells, verify output
- [ ] Test error cases (syntax errors, undefined vars)
- [ ] Clean logs, documentation

### Phase 2: Extended Functionality (2–3 weeks)

- [ ] `complete_request`: ACL2 symbol completion
- [ ] `inspect_request`: Function signatures, theorem info
- [ ] `interrupt_request`: Abort running code
- [ ] `shutdown_request`: Graceful shutdown
- [ ] `history_request`: Command history retrieval
- [ ] Rich output: HTML, LaTeX, display_data
- [ ] User input handling (input_request)

### Phase 3: Polish & Optimization (1–2 weeks)

- [ ] Performance profiling
- [ ] Memory management
- [ ] Logging infrastructure
- [ ] Edge case handling
- [ ] Documentation (README, API docs)
- [ ] Public release

---

## 11. Testing Strategy

### Unit Tests (per module)

| Module                      | Tests                                          |
|-----------------------------|------------------------------------------------|
| connection-file-parser      | Parse TCP/IPC, validate fields, missing fields|
| zmq-socket-manager          | Bind, send/recv, poll, cleanup                 |
| message-envelope            | Serialize/deserialize, HMAC sign/verify        |
| kernel-state                | Execution counter, namespace persistence       |
| request-handlers            | kernel_info, execute, error cases              |
| acl2-eval                   | Simple eval, errors, long output               |

### Integration Tests

1. **Full handshake:** kernel_info_request → reply
2. **Simple execution:** execute `(+ 1 2)` → result
3. **Output capture:** execute code with print statements → stream messages
4. **Error handling:** execute invalid code → error message
5. **Execution counter:** multiple executions → counter increments
6. **Multipart messages:** send/recv through all channels

### End-to-End Tests

- Launch kernel from Jupyter Server
- Connect JupyterLab frontend
- Create notebook, execute cells
- Verify output, errors, status updates

---

## 12. Deployment

### kernel.json

```json
{
  "display_name": "ACL2",
  "language": "acl2",
  "argv": [
    "sbcl",
    "--script",
    "/path/to/acl2-kernel/kernel-main.lisp",
    "-f",
    "{connection_file}"
  ]
}
```

### Installation

```bash
# Install kernelspec
jupyter kernelspec install /path/to/acl2-kernel/

# Verify
jupyter kernelspec list
# Should show: acl2  /home/user/.local/share/jupyter/kernels/acl2

# Launch
jupyter lab
# Select ACL2 kernel in notebook
```

---

## 13. Error Handling & Edge Cases

### Parsing Errors

- **Unmatched parentheses:** Catch read error, publish error message
- **Undefined functions:** Catch evaluation error, preserve state
- **Infinite loops:** Timeout mechanism (future: interrupt_request)

### Transport Errors

- **Socket bind failure:** Log, exit gracefully
- **Message corruption:** Verify HMAC, discard if invalid
- **Connection drop:** Kernel continues (Jupyter Server will restart)

### Concurrency

- **Multiple execute requests:** Queue or serialize (simple: sequential)
- **Heartbeat during execute:** Background thread ensures heartbeat responds
- **Shutdown during execute:** Finish current execution, then exit

---

## 14. Future Enhancements

- **Async execution:** Allow long-running code without blocking heartbeat
- **Kernel restart:** Preserve history, reset namespace
- **Custom display hooks:** Rich formatting for ACL2 objects
- **Debugger integration:** Interactive debugging in notebook
- **MCP bridge:** Connect to Model Context Protocol servers
- **Wiki3 integration:** Query/update knowledge graphs

---

## Appendix: Useful References

- **Jupyter Protocol:** https://jupyter-client.readthedocs.io/en/latest/messaging.html
- **ZeroMQ Guide:** https://zguide.zeromq.org/
- **ACL2 Documentation:** https://www.cs.utexas.edu/users/moore/acl2/
- **SBCL Manual:** http://sbcl.org/manual/
- **CCL Documentation:** https://ccl.clozure.com/

---

**Document Version:** 1.0  
**Created:** 2026-01-15  
**Status:** Ready for implementation
