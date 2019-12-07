VerifiedHardware
======================


Introduction
------------

This project intends to build a verified version of [microsoft/RIoT](https://github.com/microsoft/RIoT) using 
- [F*](https://github.com/FStarLang/FStar): verification system for effectful programs
- [KreMLin](https://github.com/FStarLang/kremlin): a tool for extracting low-level F* programs to readable C code
- [HACL*](https://github.com/project-everest/hacl-star): a formally verified cryptographic library written in F*

Current Status
--------------

[x] Loader interface of the DICE layer (in **[master](https://github.com/95616ARG/VerifiedHardware/tree/master)** branch) 

[x] RIoT prototype (in **[zt-riot-minimal](https://github.com/95616ARG/VerifiedHardware/tree/zt-riot-minimal)** branch)

Build C files
--------------

### Directory structure

```
.
├── src                   # F* source codes directory
│   ├── Minimal.DICE.fst      # `Minimal.DICE` module
│   └── Makefile              # compile F* source codes to C
├── out                   # generated C codes dicevtory
│   ├── Minimal_DICE.h        # `Minimal` DICE header file
│   ├── Minimal_DICE.c        # `Minimal` DICE code
│   └── ...                   # auto-generated third-party C files
├── .docker               # docker file 
│   ├── Dockerfile 
│   └── .emacs                # config for emacs user
└── README.md
```

### Dependencies
- F*: [master](https://github.com/FStarLang/FStar) branch
- KreMLin: [master](https://github.com/FStarLang/kremlin) branch
- HACL*: [fstar-master](https://github.com/project-everest/hacl-star/tree/fstar-master) branch
### (*optional*) Build and use docker image
```
$ sudo docker build -t verifiedhardware:minimal -f .docker/base/Dockerfile .
$ sudo docker run -it --rm verifiedhardware:minimal bash
```
Run the commands above and you will be in the project root directory. This Dockerfile depends on the official F* build packaged with Emacs : [fstarlang/fstar-emacs:latest](https://hub.docker.com/r/fstarlang/fstar-emacs/tags).

### Build C file
Run `Makefile` under the project root directory to build C files into `./out`.
```
$ make
```
