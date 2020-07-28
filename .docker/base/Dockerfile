FROM fstarlang/fstar-emacs:latest

MAINTAINER Zhe Tao <zhetao@ucdavis.edu>;

COPY --chown=build .docker/.emacs .emacs

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
  sudo apt install -y time

# Set ENV
ENV FSTAR_HOME=home/build/FStar
ENV KREMLIN_HOME=home/build/kremlin
ENV VALE_HOME=home/build/vale
ENV MLCRYPTO_HOME=home/build/vale
ENV HACL_HOME=home/build/hacl-star

# Fetch Sources
RUN git clone https://github.com/FStarLang/kremlin.git ${KREMLIN_HOME} && \
  git clone https://github.com/project-everest/hacl-star.git ${HACL_HOME} && \
  wget https://github.com/project-everest/vale/releases/download/v0.3.13/vale-release-0.3.13.zip && \
  unzip vale-release-0.3.13.zip && \
  mv vale-release-0.3.13 /home/build/vale

# Update FStar and KreMLin
RUN eval $(opam env) && \
  cd ${FSTAR_HOME} && \
  git checkout -- . && \
  git clean -fdx && \
  git pull && \
  make -C src/ocaml-output && \
  OTHERFLAGS='--admit_smt_queries true' make -C ulib -j 32 && \
  make -C ulib/ml -j 32 && \
  cd ${KREMLIN_HOME} && \
  OTHERFLAGS='--admit_smt_queries true' make -j 32

# Build hacl-star
RUN cd ${HACL_HOME} && \
  OTHERFLAGS="--admit-smt-queries=true" make verify-hacl -j32

# Set fstar.exe and krml
RUN sudo ln -s ${FSTAR_HOME}/bin/fstar.exe /usr/local/bin/fstar.exe
RUN sudo ln -s ${KREMLIN_HOME}/krml /usr/local/bin/krml

# Copy VerifiedHardware
COPY --chown=build . /home/build/VerifiedHardware

# Switch to the project root directory
WORKDIR /home/build/VerifiedHardware
