# ACL2 GUIX Package

This directory contains a GUIX package definition for ACL2 (A Computational Logic for Applicative Common Lisp) running on SBCL (Steel Bank Common Lisp).

## Files

- `acl2.scm` - Main GUIX package definition for ACL2
- `manifest.scm` - GUIX manifest for easy installation
- `.guix-channel` - Channel definition to use this repo as a GUIX channel

## Usage

### Method 1: Using the package definition directly

```bash
# build ACL2 using the local package definition
guix build -f acl2.scm
guix install acl2

# Or create a development environment
guix shell -f acl2.scm
```

### Method 2: Using the manifest

```bash
# Install using the manifest
guix install -m manifest.scm

# Or create a development environment
guix shell -m manifest.scm
```

### Method 3: Using as a GUIX channel

1. Add this repository to your `~/.config/guix/channels.scm`:

```scheme
(cons* (channel
         (name 'acl2-channel)
         (url "https://github.com/jimwhite/acl2-docker.git")
         (branch "main"))
       %default-channels)
```

2. Update your channels:

```bash
guix pull
```

3. Install ACL2:

```bash
guix install acl2
```

## Package Details

The GUIX package:

- Downloads ACL2 source from the official GitHub repository
- Builds ACL2 using SBCL as the underlying Lisp implementation
- Certifies the "basic" book collection during build
- Installs ACL2 executable and support scripts (cert.pl, clean.pl, critpath.pl)
- Sets up proper environment variables for ACL2_SYSTEM_BOOKS

## Environment Variables

After installation, the following environment variables are recommended:

- `ACL2_SYSTEM_BOOKS` - Points to the installed books directory
- `ACL2` - Points to the ACL2 executable

These are automatically set when using the `acl2-wrapper` script.

## Comparison with Docker Build

This GUIX package provides the same functionality as the Docker build in this repository:

- Uses SBCL 2.5.3+ as the Lisp implementation
- Downloads latest ACL2 from GitHub
- Builds with `make LISP="sbcl"`
- Certifies basic books with parallel jobs
- Sets up proper paths and environment

## Building from Source

To build the package from source:

```bash
guix build -f acl2.scm
```

## Testing

After installation, you can test ACL2:

```bash
# Start ACL2 REPL
acl2

# Or use the wrapper with proper environment
acl2-wrapper

# Test with a simple example
echo "(+ 1 2 3)" | acl2-wrapper
```

## Notes

- The package builds ACL2 with SBCL's default configuration
- Book certification is done with 4 parallel jobs during build
- The installation includes certified basic books for immediate use
- Additional books can be certified using the included cert.pl script
