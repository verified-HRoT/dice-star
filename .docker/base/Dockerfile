FROM projecteverest/hacl-star-linux:0948e6ea5c89

RUN sudo ln -s ~/FStar/bin/fstar.exe /usr/local/bin/fstar.exe
RUN sudo ln -s ~/hacl-star/kremlin/krml /usr/local/bin/krml

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

ADD .emacs .emacs

RUN sudo chown everest:everest .emacs
