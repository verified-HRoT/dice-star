VerifiedHardware
======================


Introduction
------------

Hardware verification using F*

Build C files
--------------

### Directory structure

```
.
├── src                   # F* source codes directory
│   ├── Minimal.Main.fst      # main module
│   ├── Minimal.DICE.fst      # `Minimal.DICE` module
│   ├── Minimal.RIoT.fst      # `Minimal.RIoT` module
│   └── Makefile              # compile F* source codes to C
├── out                   # generated C codes dicevtory
│   ├── Minimal_Main.h        # `Minimal` header file
│   ├── Minimal_Main.c        # `Minimal` main file
│   ├── Minimal_DICE.h        # `Minimal` DICE header file
│   ├── Minimal_DICE.c        # `Minimal` DICE code
│   ├── Minimal_RIoT.h        # `Minimal` RIoT header file
│   ├── Minimal_RIoT.c        # `Minimal` RIoT file
│   └── ...                   # auto-generated third-party C files
├── .docker               # docker file 
│   ├── Dockerfile 
│   └── .emacs                # config for emacs user
└── README.md
```

### (*optional*) Build and use docker image
```
sudo docker build -t verifiedhardware:minimal -f .docker/Dockerfile .
sudo docker run -itd --name vhw --rm verifiedhardware:minimal bash
```

### Build C file
Enter F* source file directory `./src` and run `Makefile` to build C files into `./out`
```
$ cd ./src
$ make
```