FROM fstarlang/fstar-emacs:latest
MAINTAINER Zhe Tao <zhetao@ucdavis.edu>;

COPY --chown=build .docker/.emacs .emacs

# Set ENV
ENV FSTAR_HOME=/home/build/FStar
ENV KREMLIN_HOME=/home/build/kremlin
ENV VALE_HOME=/home/build/vale
ENV MLCRYPTO_HOME=/home/build/vale
ENV HACL_HOME=/home/build/hacl-star
ENV EVERPARSE_HOME=/home/build/everparse

# Fix F* and all dependencies to tested versions
ARG FSTAR_VERSION=771b5c9c151b8c7b835060d3dd2646ef265f0393
ARG HACL_VERSION=27912218150663a51d7aebf69286a6cd778609b1
ARG KREMLIN_VERSION=5d03de710d31220ba0f2ce7d7725c3e74a797b96
ARG EVERPARSE_VERSION=b2e464d4838e74edcb96921637becd494e2a6b9f

# make -j parameter
ARG NJOB=4

# Handle dependencies for kremlin
RUN opam install -y -q \
  ppx_deriving_yojson \
  zarith \
  pprint \
  menhir \
  sedlex \
  process \
  fix \
  wasm \
  visitors

RUN sudo apt update && \
  sudo apt install -y time xxd

RUN sudo ln -fs /usr/share/zoneinfo/America/New_York /etc/localtime &&\
  DEBIAN_FRONTEND=noninteractive sudo apt install -y tzdata &&\
  sudo dpkg-reconfigure --frontend noninteractive tzdata &&\
  sudo apt install -y mono-devel

# Fetch Sources
RUN git clone https://github.com/FStarLang/kremlin.git ${KREMLIN_HOME} && \
  git clone https://github.com/project-everest/hacl-star.git ${HACL_HOME} && \
  git clone https://github.com/project-everest/everparse.git ${EVERPARSE_HOME} && \
  wget https://github.com/project-everest/vale/releases/download/v0.3.13/vale-release-0.3.13.zip && \
  unzip vale-release-0.3.13.zip && \
  mv vale-release-0.3.13 /home/build/vale

# Update FStar
WORKDIR ${FSTAR_HOME}
RUN eval $(opam env) && \
  cd ${FSTAR_HOME} && \
  git checkout -- . && \
  git clean -fdx && \
  git pull &&\
  git checkout ${FSTAR_VERSION} && \
  make -C src/ocaml-output && \
  OTHERFLAGS='--admit_smt_queries true' make -C ulib -j ${NJOB} && \
  make -C ulib/ml -j ${NJOB} && \
  sudo ln -s ${FSTAR_HOME}/bin/fstar.exe /usr/local/bin/fstar.exe

# Update KreMLin
WORKDIR ${KREMLIN_HOME}
RUN eval $(opam env) && \
  cd ${KREMLIN_HOME} && \
  git checkout -- . && \
  git clean -fdx && \
  git pull && \
  git checkout ${KREMLIN_VERSION} && \
  OTHERFLAGS='--admit_smt_queries true' make -j ${NJOB} && \
  sudo ln -s ${KREMLIN_HOME}/krml /usr/local/bin/krml

# Build hacl-star
WORKDIR ${HACL_HOME}
RUN eval $(opam env) && \
  git checkout ${HACL_VERSION} && \
  OTHERFLAGS='--admit_smt_queries true' make verify-hacl -j ${NJOB}

WORKDIR ${EVERPARSE_HOME}/src/lowparse
RUN git checkout ${EVERPARSE_VERSION} && \
  OTHERFLAGS='--admit_smt_queries true' make verify-all -j ${NJOB}

# Copy VerifiedHardware
COPY --chown=build . /home/build/VerifiedHardware

# Switch to the project root directory
WORKDIR /home/build/VerifiedHardware
RUN git checkout -- . && git clean -fdx
