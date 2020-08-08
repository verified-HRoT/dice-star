FROM fstarlang/fstar-emacs:latest
# FROM projecteverest/hacl-star-linux:912ee384e197

# ENV EVERPARSE_HOME=/home/everest/everparse
# ENV KREMLIN_HOME=/home/everest/hacl-star/kremlin

# RUN git clone https://github.com/project-everest/everparse.git
# WORKDIR ${EVERPARSE_HOME}/src/lowparse
# RUN OTHERFLAGS='--admit_smt_queries true' make verify-all -j32

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
ENV FSTAR_HOME=/home/build/FStar
ENV KREMLIN_HOME=/home/build/kremlin
ENV VALE_HOME=/home/build/vale
ENV MLCRYPTO_HOME=/home/build/vale
ENV HACL_HOME=/home/build/hacl-star

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
  git pull &&\
  git checkout 771b5c9c151b8c7b835060d3dd2646ef265f0393 && \
  make -C src/ocaml-output && \
  OTHERFLAGS='--admit_smt_queries true' make -C ulib -j 32 && \
  make -C ulib/ml -j 32 && \
  cd ${KREMLIN_HOME} && \
  git checkout -- . && \
  git clean -fdx && \
  git pull && \
  git checkout 5d03de710d31220ba0f2ce7d7725c3e74a797b96 && \
  OTHERFLAGS='--admit_smt_queries true' make -j 32

# Set fstar.exe and krml
RUN sudo ln -s ${FSTAR_HOME}/bin/fstar.exe /usr/local/bin/fstar.exe
RUN sudo ln -s ${KREMLIN_HOME}/krml /usr/local/bin/krml

RUN sudo ln -fs /usr/share/zoneinfo/America/New_York /etc/localtime &&\
  DEBIAN_FRONTEND=noninteractive sudo apt install -y tzdata &&\
  sudo dpkg-reconfigure --frontend noninteractive tzdata &&\
  sudo apt install -y mono-devel

# Build hacl-star
RUN eval $(opam env) && \
  cd ${HACL_HOME} && \
  git checkout 27912218150663a51d7aebf69286a6cd778609b1 && \
  OTHERFLAGS='--admit_smt_queries true' make verify-hacl -j32

ENV EVERPARSE_HOME=/home/build/everparse
RUN git clone https://github.com/project-everest/everparse.git
WORKDIR ${EVERPARSE_HOME}/src/lowparse
RUN git checkout b2e464d4838e74edcb96921637becd494e2a6b9f && \
  OTHERFLAGS='--admit_smt_queries true' make verify-all -j32

# Copy VerifiedHardware
COPY --chown=build . /home/build/VerifiedHardware

# Switch to the project root directory
WORKDIR /home/build/VerifiedHardware
RUN git checkout -- . && git clean -fdx
