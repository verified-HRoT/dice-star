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

# Build kremlin
ENV KREMLIN_HOME=/home/build/kremlin
RUN git clone https://github.com/FStarLang/kremlin.git ${KREMLIN_HOME}
WORKDIR ${KREMLIN_HOME}
RUN eval $(opam env); make -j 32

# Get hacl-star
ENV HACL_HOME=/home/build/hacl-star
RUN git clone https://github.com/project-everest/hacl-star.git ${HACL_HOME}
WORKDIR ${HACL_HOME}
RUN git checkout fstar-master

# Set fstar.exe and krml
RUN sudo ln -s ${FSTAR_HOME}/bin/fstar.exe /usr/local/bin/fstar.exe
RUN sudo ln -s ${KREMLIN_HOME}/krml /usr/local/bin/krml

# Copy VerifiedHardware
COPY --chown=build . /home/build/VerifiedHardware

# Switch to the project root directory
WORKDIR /home/build/VerifiedHardware