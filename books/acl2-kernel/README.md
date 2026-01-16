# ACL2 Native Jupyter Kernel

A native ACL2 Jupyter kernel implemented in ACL2/Lisp.

## Installation

```bash
cd /workspaces/acl2-jupyter/books/acl2-kernel/install
./install.sh
```

The install script will:
1. Register the kernel with Jupyter
2. Pre-compile dependencies to populate the FASL cache

## Usage

After installation, start Jupyter and select "ACL2" as the kernel.

## Troubleshooting

### Kernel startup timeout

**Symptom:** The kernel fails to start or times out during `wait_for_ready`.

**Cause:** If the FASL cache (`~/.cache/common-lisp/`) is empty or was cleared, 
the kernel must compile all Quicklisp dependencies (pzmq, cffi, etc.) on first 
startup. This compilation can take several minutes, exceeding Jupyter's default 
startup timeout.

**Solution:** Pre-populate the cache by running the kernel once manually:

```bash
cd /workspaces/acl2-jupyter/books/acl2-kernel
echo '(include-book "top") :q (quit)' | /home/acl2/saved_acl2
```

Or re-run the install script, which does this automatically.

**Note:** This same issue affects `common-lisp-jupyter` and any other Lisp-based
Jupyter kernel that uses Quicklisp. If you clear the cache, all Lisp kernels 
will need to recompile on next startup.

### Development tip

When developing or testing the kernel, avoid clearing `~/.cache/common-lisp/` 
unless necessary. If you must clear it, pre-compile the dependencies before 
testing with Jupyter.
