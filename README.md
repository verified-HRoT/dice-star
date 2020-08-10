Verified DICE/RIoT Implementation
======================


Introduction
------------

This project intends to build a verified version of [microsoft/RIoT](https://github.com/microsoft/RIoT) using
- [F*](https://github.com/FStarLang/FStar): verification system for effectful programs
- [KreMLin](https://github.com/FStarLang/kremlin): a tool for extracting low-level F* programs to readable C code
- [HACL*](https://github.com/project-everest/hacl-star): a formally verified cryptographic library written in F*
- [EverParse](https://github.com/project-everest/everparse): a F* library for write secure parser and serializer


File Organization
-----------------

```
      ASN.1
     /  |
  X.509 |   C        C
     \  |  /         |
       RIoT         DICE
```

- `src/c`: C source files
- `src/dice`: F* source files for DICE
- `src/riot`: F* source files for RIoT
  - `RIoT.Base`: X.509 base definitions
  - `RIoT.Declassify`: Interface for declassification functions
  - `RIoT.X509.*`: X.509 certificate-related definitions
  - `RIoT.Spec.*`: Specification for crypto and X.509 certificate-related functions
  - `RIoT.Impl.*`: Implementation for crypto and X.509 certificate-related functions
  - `RIoT.Core`: RIoT Core functionality
  - `src/riot/asn1`: F* source files for ASN.1 serializer
    - `ASN1.Base`: Base ASN.1 definitions
    - `ASN1.Spec.*`: Specification serializers and combinators
    - `ASN1.Low.*`: Implementation serializers and combinators
  - `src/riot/x509`: F* source files for X.509 serializer
    - `X509.Base`: X.509 base definitions
    - `X509.Crypto`:  Crypto-related serializer
    - `X509.BasicFields`: Serializer for X.509 certificate basic fields
    - `X509.ExtFields`: Serializer for X.509 certificate extension fields
- `src/test` Test scripts
- `src/obj` F* outputs (after build)


Installation
------------
### (recommend) Docker
Execute the following command and you will be in the project root directory. This Dockerfile depends on the official F* build packaged with Emacs : [fstarlang/fstar-emacs:latest](https://hub.docker.com/r/fstarlang/fstar-emacs/tags).
```
$ sudo docker build -t verifiedhardware:checkpoint -f .docker/base/Dockerfile .
$ sudo docker run -it --rm verifiedhardware:checkpoint bash
```


Build and Test
--------------
You can prepend `OTHERFLAGS='--admit_smt_queries true'` before any commands below to (largely) speed up the verification process (by assuming SMT queries) if you are sure the F* definitions are correct.

### Verify F* Source Files
You can verify F* source files for any project (and their dependencies) of `DICE`, `RIoT`, `ASN1` and `X509` by entering the corresponding directory and executing
```
make verify-all -j4
```

### Test Projects (and Generate C Files)
You can test `RIoT` or `ASN1` by executing
```
make test-riot -j4
```
or
```
make test-asn1 -j4
```
at the `src/test` directory or the root directory. The test executable `src/test/test.exe` will be complied and executed. Generated C files lie in `src/obj`.

### Generate C Files for RIoT
After executing
```
make test-riot -j4
```
C files will be generated in `src/obj`.
