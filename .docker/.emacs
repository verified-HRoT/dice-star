(require 'package)
(add-to-list 'package-archives '("melpa" . "http://melpa.org/packages/") t)
(package-initialize)
(set-default 'fstar-executable "~/FStar/bin/fstar.exe")
(global-flycheck-mode)
(set-face-font 'default "Terminus-14")


;;set fstar includes
(setq fstar-subp-prover-args
      '(
        ;; "--query_stats"
        "--include"
        "/home/everest/hacl-star/kremlin/kremlib"
        "--include"
        "/home/everest/hacl-star/specs"
        "--include"
        "/home/everest/hacl-star/specs/lemmas"
        "--include"
        "/home/everest/hacl-star/code/hash"
        "--include"
        "/home/everest/hacl-star/code/hkdf"
        "--include"
        "/home/everest/hacl-star/code/hmac"
        "--include"
        "/home/everest/hacl-star/code/curve25519"
        "--include"
        "/home/everest/hacl-star/code/ed25519"
        "--include"
        "/home/everest/hacl-star/lib"
        "--include"
        "/home/everest/hacl-star/providers/evercrypt"))
