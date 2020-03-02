;;============================================================>==
;; base configure for common using
;;=============================================================
;; start server , 这样在终端下主可以通过emacsclient -n 直接于GUI emacs打开文件
(require 'server)
(unless (server-running-p "server")
(server-start))

;; Added by Package.el.  This must come before configurations of
;; installed packages.  Don't delete this line.  If you don't want it,
;; just comment it out by adding a semicolon to the start of the line.
;; You may delete these explanatory comments.
(package-initialize)
(require 'package)
(add-to-list 'package-archives
             '("melpa-stable" . "https://stable.melpa.org/packages/"))
(package-initialize)

;; package server
;; (setq package-archives '(("gnu" . "http://elpa.gnu.org/packages/")
;; ("melpa-stable" . "https://stable.melpa.org/packages/")))

;; (setq package-archives '(("gnu" . "http://elpa.gnu.org/packages/")
;; ("melpa-stable" . "https://stable.melpa.org/packages/")
;; ("marmalade" . "http://marmalade-repo.org/packages/")
;; ("melpa" . "http://melpa.milkbox.net/packages/")))

;; background color , 苹果绿，爱护眼睛
(when window-system
  (custom-set-faces
   '(default ((t (:background "#B4EEB4"))))))
(custom-set-variables
 ;; custom-set-variables was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(package-selected-packages (quote (company))))
(custom-set-faces
 ;; custom-set-faces was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 )
(add-hook 'after-init-hook 'global-company-mode)
;;(add-to-list 'load-path "/path/to/company")
;;(autoload 'company-mode "company" nil t)
(add-hook 'c++-mode-hook 'global-company-mode)
(add-hook 'c-mode-hook 'global-company-mode)
(add-to-list 'load-path "~/.emacs.d")
(display-time-mode 1)
(setq display-time-24hr-format f)
(setq display-time-day-and-date t)
(setq global-font-lock-mode 1)
(setq 'yes-or-no-p 'y-or-n-p)
(require 'cursor-change)
(cursor-change-mode 1)

(defun open-eshell ()
  "Open eshell in other buffer"
  (interactive)
  (split-window-vertically)
  (eshell))
;;==配置auto-complete。内容较多单独放一个目录。==============
(add-to-list 'load-path "~/.emacs.d/plugins/auto-complete")
;;cl-lib.el在v24中才出现，v23是没有的，要单独下载。
(require 'auto-complete)
(require 'auto-complete-config)


;; 开启全局设定(包含哪些模式在ac-modes里查看)
;;(global-auto-complete-mode t)
