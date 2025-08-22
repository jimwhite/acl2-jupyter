# ACL2-Jupyter Docker Image

Use *A Computational Logic for Applicative Common Lisp (ACL2)* in Jupyter notebooks running in a container with just a command or two. 

## Availability

This image is available on the GitHub Container Registry at [`jimwhite/acl2-jupyter`](https://ghcr.io/jimwhite/acl2-jupyter).

The project source is at https://github.com/jimwhite/acl2-jupyter.

## Credits
This project is built from:

* https://github.com/mister-walter/acl2-docker by [Andrew Walter](https://www.atwalter.com/)
* https://github.com/yitzchak/common-lisp-jupyter along with several other repos by [Tarn Burton](https://github.com/yitzchak)
* https://github.com/tani/acl2-kernel by [Masaya Taniguchi](https://tani.cc/).
* https://github.com/rubengamboa/acl2-docker-images by [Ruben Gamoa](https://www.uwyo.edu/eecs/faculty-staff/faculty/ruben-gamboa/index.html)

## Using a prebuilt image locally

By default, running this Docker image will launch the JupyterLab server on port 8888.  

```bash
docker pull ghcr.io/jimwhite/acl2-jupyter:latest
docker run -it --rm -p 8888:8888 -v $(PWD):/home/jovyan/work acl2-jupyter
```

To get the CLI just supply the command.  For SBCL and ACL2 in a terminal you'll want `rlwrap`.

```bash
docker run -it --rm -v $(PWD):/home/jovyan/work acl2-jupyter rlwrap acl2
```

Using `sudo` within the container does not require a password.

## Using a prebuilt image in a GitHub Codespace (free!)

There is a [devcontainer.json](https://github.com/jimwhite/acl2-jupyter/blob/main/.devcontainer/devcontainer.json) file in the [repo](https://github.com/jimwhite/acl2-jupyter) so use the "New codespace" action in the "+" dropdown (middle of the buttons at top right of the repo page) then enter "jimwhite/acl2-jupyter" for "Select repository".  The smallest machine type is 2 CPUs which is plenty.

<div style="display: flex; align-items: center;">
  <img src="img/s13292008202025.png" alt="Dropdown: New codespace" width="320"/>
  <img src="img/s13372308202025.png" alt="Select repository: jimwhite/acl2-jupyter" width="320"/>
</div>
<div style="display: flex; align-items: center;">
  <img src="img/s12161208202025.png" alt="Create new codespace" width="320"/>
  <img src="img/s13460808202025.png" alt="Building codespace..." width="320"/>
</div>

It takes a few minutes to build the codespace because the image is fairly large (~10GB).  After it loads there may be some messages about various extensions loading or not and such but they can (probably) be ignored.  Choose "My codespaces" from the top left menu icon, then select the codespace for the "jimwhite/acl2-jupyter" repo, click "Show more actions for this codespace" (... menu at the right), and choose "Open in JupyterLab".

<div style="display: flex; align-items: center;">
<img src="img/s13565108202025.png" alt="My codespaces" width="320"/>
<img src="img/s14021208202025.png" alt="Open in JupyterLab" width="320"/>
</div>

And success!

![JupyterLab with Python3, ACL2, and SBCL](img/s14075208202025.png)

The Free Tier on GitHub gets 120 CPU hours free: https://docs.github.com/en/billing/concepts/product-billing/github-codespaces.  The small dual CPU is $0.18 per hour after the free allocation.

But GitHub recently deployed budgets for all billed services with $0 allocation by default; so if you get a "Billing Error" message, go to your billing settings and set appropriate quotas.

## Old Usage

By default, running this Docker image will drop you into the ACL2 REPL. The "basic" selection of books (per the ACL2 Makefile) has been certified, but you may want to certify additional books. One way to do this is to start a Docker container with a shell rather than ACL2; one can do that with a command like `docker run -it atwalter/acl2 /bin/bash`. Then, one can use [cert.pl](https://www.cs.utexas.edu/~moore/acl2/manuals/current/manual/?topic=BUILD____CERT.PL) to certify some books before starting ACL2. A full example is shown below, where lines prefixed by `$` indicate commands executed outside of Docker and `#` indicate commands executed inside of the Docker container.

```
$ docker run -it atwalter/acl2 /bin/bash
# cert.pl ~/acl2/books/sorting/isort
# acl2
# ACL2 !> (include-book "sorting/isort" :dir :system)
# ACL2 !> (isort '(5 2 1 4 3))
(1 2 3 4 5)
```

Note that when the Docker container exits, the certificates for any books certified since the container was started will be lost. If you find yourself repeatedly needing to certify the same set of books, you can create a new Docker image based on this one. You can find an example Dockerfile in `examples/certified-books/Dockerfile`.

## Building

The [`jq`](https://github.com/stedolan/jq) command-line tool must be installed to use the provided `Makefile` to build an ACL2 Docker image. This tool is used to get the latest commit hash for the ACL2 repo from Github.

So `which jq` and then `brew install jq` or `sudo apt-get install jq` as appropriate if not already installed.

This project uses several submodules from https://github.com/yitzchak. Either use `git clone --recurse-submodules` or run `make git-submodules` to sync those files.

```bash
git clone https://github.com/jimwhite/acl2-jupyter.git
cd acl2-jupyter
make git-submodules
make
make run
```

The `make run` will run sharing the CWD as above (`docker run -it -p 8888:8888 -v $(PWD):/home/jovyan/work acl2-jupyter`).

To enable reproducible builds and reduce image size, image build time, and download bandwidth during a build, the Dockerfile expects that it is provided a `ACL2_REPO_LATEST_COMMIT` build argument. This argument must be set to a URL-safe string corresponding to a commit or tag format that Github understands. I have tested this with full commit hashes and short commit hashes (e.g. the first 8 characters of the full commit hash). As suggested above, the `build` make target will  use Github's API to determine the commit hash for the latest commit to the ACL2 repo and pass that to Docker when building an image.

### Multi-Platform Building

This image is now built and distributed as a multi-platform Docker image. This means that both a `linux/amd64` and `linux/arm64` version of the image are built, and Docker should automatically use the appropriate version for your computer's architecture.

The images on Docker Hub and the GitHub Container Registry are built using the `build-multiplatform` and `build-multiplatform-ghcr` make targets. To use these targets, you need to be using a Docker builder that is capable of building for both the `linux/amd64` and `linux/arm64` platforms. macOS' emulation for `linux/amd64` is at present insufficient, as it does not emulate FPU traps and ACL2 expects these traps to occur. So, I build the images using a Docker builder that consists of two nodes (an Apple Silicon machine and an x86-64 machine). The best information I've found on how to do this is in [this Medium post](https://medium.com/@spurin/using-docker-and-multiple-buildx-nodes-for-simultaneous-cross-platform-builds-cee0f797d939).

## Notes

By default, certification is done with 4 parallel tasks. This can be changed by overriding the `ACL2_CERT_JOBS` variable of the Makefile. For example, to use 2 tasks instead, run `make build ACL2_CERT_JOBS=2`.

To provide additional arguments to the `make` command that will be used to build ACL2's books, you can override the `ACL2_CERTIFY_OPTS` variable of the Makefile. Notice that this will override the effects of the `ACL2_CERT_JOBS` variable, so you will need to provide the appropriate `-j` option in that case.

By default, the "basic" book selection is certified. This can be changed by overriding the `ACL2_CERTIFY_TARGETS` build argument. Multiple targets can be provided to this argument if desired.

## Sources

```bash
# sha256 of quicklisp.lisp = 4a7a5c2aebe0716417047854267397e24a44d0cce096127411e9ce9ccfeb2c17
wget -kL -P context https://beta.quicklisp.org/quicklisp.lisp

git submodule add https://github.com/jimwhite/acl2-kernel.git context/acl2-kernel
git submodule add https://github.com/yitzchak/archlinux-cl.git context/archlinux-cl
git submodule add https://github.com/yitzchak/common-lisp-jupyter.git context/quicklisp/local-projects/common-lisp-jupyter
git submodule add https://github.com/yitzchak/delta-vega.git context/quicklisp/local-projects/delta-vega
git submodule add https://github.com/yitzchak/resizable-box-clj.git context/quicklisp/local-projects/resizable-box-clj
git submodule add https://github.com/yitzchak/ngl-clj.git context/quicklisp/local-projects/ngl-clj
```

* https://github.com/jimwhite/acl2-kernel.git context/acl2-kernel is forked from https://github.com/tani/acl2-kernel to bring it up-to-date.

* https://github.com/jimwhite/acl2-jupyter itself is forked from https://github.com/mister-walter/acl2-docker (and was unforked due to a GitHub permissions confusion and can't be undone).

### Base Image

ACL2-Jupyter uses the [quay.io/jupyter/minimal-notebook:latest](https://quay.io/repository/jupyter/minimal-notebook) image (source https://github.com/jupyter/docker-stacks/tree/main/images/minimal-notebook) because we want the JupyterLab stuff to work and we're gonna build SBCL and ACL2 the way we want anyhow.  Note that the DockerHub image is no longer updated.

For a full complement of Python support including PySpark use BASE_IMAGE=[quay.io/jupyter/pyspark-notebook:latest](https://quay.io/repository/jupyter/pyspark-notebook) image (source https://github.com/jupyter/docker-stacks/tree/main/images/pyspark-notebook)

## Moar Information

* *ACL2* home page at UT Austin https://www.cs.utexas.edu/~moore/acl2/acl2-doc.html
* *Hyper-Card for ACL2 Programming* https://www.cs.utexas.edu/~moore/publications/hyper-card.html
* *ACL2 versions of (some of) the Top 100 Theorems List* https://acl2.org/doc/?topic=ACL2____100-THEOREMS
* *ACL2 Documentation* https://acl2.org/doc
* *ACL2 Community* https://acl2.org/doc/?topic=ACL2____COMMUNITY
* *ACL2 Workshops*  https://acl2.org/doc/?topic=ACL2____WORKSHOPS
* *An ACL2(s) Interface to Z3* by Walter and Manolios, ACL2 2025 https://cgi.cse.unsw.edu.au/~eptcs/paper.cgi?ACL2in2025.10
* *Advances in ACL2 Proof Debugging Tools* by Kaufman and Moore, ACL2 2023 https://cgi.cse.unsw.edu.au/~eptcs/paper.cgi?ACL22023.7
* *Using ACL2 To Teach Students About Software Testing* by Gamboa and Thoney ACL2 2022 https://arxiv.org/abs/2205.11695
* *ACL2(ml): Machine-Learning for ACL2* by Heras and Komendantskaya ACL2 2014 https://arxiv.org/abs/1404.3034
* https://github.com/s-expressionists - active community developing kewl new CL packages

