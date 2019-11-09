FROM projecteverest/hacl-star-linux:0948e6ea5c89

LABEL MAINTAINER="zhetao@ucdavis.edu"

RUN sudo ln -s ~/FStar/bin/fstar.exe /usr/local/bin/fstar.exe
RUN sudo ln -s ~/hacl-star/kremlin/krml /usr/local/bin/krml

COPY . VerifiedHardware

# Prepare and build Z3
ENV z3=z3-4.8.5-x64-debian-8.11
ADD https://github.com/FStarLang/binaries/raw/master/z3-tested/${z3}.zip .
RUN sudo unzip ${z3}.zip
ENV PATH=/home/everest/${z3}/bin:${PATH}

# Install required packages
RUN sudo apt-get install -y emacs libglu1-mesa xfonts-terminus fonts-symbola

ENV LANG C.UTF-8
RUN emacs --batch \
        --eval "(require 'package)" \
        --eval "(add-to-list 'package-archives '(\"melpa\" . \"http://melpa.org/packages/\") t)" \
        --eval "(package-initialize)" \
        --eval "(package-refresh-contents)" \
        --eval "(package-install 'fstar-mode)" \
        --eval "(package-install 'flycheck)"

ADD .docker/.emacs .emacs
RUN sudo chown everest:everest .emacs
