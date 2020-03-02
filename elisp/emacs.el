(defun copy-this-word ()
  (interactive)
  (save-excursion
    (let (pt)
    (skip-chars-backward "-_A-Za-z0-9")
    (setq pt (point))
    (skip-chars-forward "-_A-Za-z0-9")
    (set-mark pt)
    (kill-ring-save (region-beginning) (region-end)))))

(defun select-current-line ()
  "Select the current line"
  (interactive)
  (let ((pos (line-beginning-position)))
    (end-of-line)
    (set-mark pos)))

(defun copy-this-line ()
  (interactive)
  (save-excursion
    (kill-ring-save (line-beginning-position) (line-end-position))))

(global-set-key "\M-w"
(lambda ()
  (interactive)
  (if mark-active
      (kill-ring-save (region-beginning)
      (region-end))
    (progn
     (kill-ring-save (line-beginning-position)
     (line-end-position))
     (message "copied line")))))
