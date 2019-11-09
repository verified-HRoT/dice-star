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
        "/home/build/kremlin/kremlib"
        "--include"
        "/home/build/hacl-star/specs"
        "--include"
        "/home/build/hacl-star/specs/lemmas"
        "--include"
        "/home/build/hacl-star/code/hash"
        "--include"
        "/home/build/hacl-star/code/hkdf"
        "--include"
        "/home/build/hacl-star/code/hmac"
        "--include"
        "/home/build/hacl-star/code/curve25519"
        "--include"
        "/home/build/hacl-star/code/ed25519"
        "--include"
        "/home/build/hacl-star/lib"
        "--include"
        "/home/build/hacl-star/providers/evercrypt"))
