;; This buffer is for text that is not saved, and for Lisp evaluation.
;; To create a file, visit it with <open> and enter text in its buffer.

(defun yay ()
  "Insert “Yay!” at cursor position."
  (interactive)
  (insert "Yay!"))

;; return the name of current buffer
(buffer-name)

;; return the full path of current file
(buffer-file-name)

;; get dir path
(file-name-directory full-path)

;; get filename part
(file-name-nondirectory full-path)

;; get filename's suffix
(file-name-extension file-name)

;; get filename sans suffix
(file-name-sans-extension file-name)

(defun select-current-word ()
  "Select the word under cursor.
“word” here is considered any alphanumeric sequence with “_” or “-”."
  (interactive)
  (let (pt)
    (skip-chars-backward "-_A-Za-z0-9")
    (setq pt (point))
    (skip-chars-forward "-_A-Za-z0-9")
    (set-mark pt)))

;; turn on highlight selection
(transient-mark-mode 1)

(defun select-current-line ()
  "Select the current line"
  (interactive)
  (let ((pos (line-beginning-position)))
    (end-of-line)
    (set-mark pos)))

(defun copy-this-word ()
  (interactive)
  (save-excursion
    (let (pt)
    (skip-chars-backward "-_A-Za-z0-9")
    (setq pt (point))
    (skip-chars-forward "-_A-Za-z0-9")
    (set-mark pt)
    (kill-ring-save (region-beginning) (region-end)))))

(defun replace-greek-region ()
  "Replace “alpha” to “α” and other greek letters in current region."
  (interactive)
  (let (
        (p1 (region-beginning))
        (p2 (region-end)))
    (save-restriction
      (narrow-to-region p1 p2)
      (goto-char (point-min))
      (while (search-forward " alpha" nil t)
        (replace-match " α" nil t))
      (goto-char (point-min))
      (while (search-forward " beta" nil t)
        (replace-match " β" nil t))
      (goto-char (point-min))
      (while (search-forward " gamma" nil t)
        (replace-match " γ" nil t)))))

(defun delete-enclosed-text ()
  "Delete texts between any pair of delimiters."
  (interactive)
  (save-excursion
    (let (p1 p2)
      (skip-chars-backward "^([<>“")
      (setq p1 (point))
      (skip-chars-forward "^)]<>”")
      (setq p2 (point))
       (delete-region p1 p2))))
	

(defun remove-line-breaks ()
  "Remove line endings in current paragraph."
  (interactive)
  (let ((fill-column (point-max)))
    (fill-paragraph nil)))


(random t)

(defun insert-random-number ()
  "Insert a random number between 0 to 999999."
  (interactive)
  (insert (number-to-string (random 999999))))

(defun delete-current-file ()
  "Delete the file associated with the current buffer.
  Delete the current buffer too.
  If no file is associated, just close buffer without prompt for save."
  (interactive)
  (let ((currentFile (buffer-file-name)))
    (when (yes-or-no-p (concat "Delete file?: " currentFile))
      (kill-buffer (current-buffer))
      (when currentFile
        (delete-file currentFile)))))

(defun highlite-it ()
  "Highlight certain lines…"
  (interactive)
  (if (equal "log" (file-name-extension (buffer-file-name)))
      (progn
        (highlight-lines-matching-regexp "ERROR:" 'hi-red-b)
        (highlight-lines-matching-regexp "NOTE:" 'hi-blue-b))))

(add-hook 'find-file-hook 'highlite-it)

(while test body)

(setq x 0)

(while (< x 4)
  (print (format "number is %d" x))
  (setq x (1+ x)))

;; move cursor by 9 chars
(forward-char 9)
(backward-char 9)

;; move cursor to position 392
(goto-char 392)

;; move cursor to the location of string "cat"
;; returns the new position
(search-forward "cat")
(search-backward "cat")

;; move cursor to the location matched by regex
;; returns the new position
(re-search-forward myRegex)
(re-search-backward myRegex)

;; preserve user's narrow-to-region
;; useful when you want to narrow-to-region in your code to work in just that region
(save-restriction
  (narrow-to-region pos1 pos2)
  ;; lisp code here
  )

;; join strings
(concat "some" "thing")

;; check if a string matches a pattern
(string-match myRegex myStr)

(rename-file "/home/joe/test1.txt" "/home/joe/test2.txt")

(copy-file "/home/joe/test1.txt" "/home/joe/test2.txt")

(delete-file "/home/joe/test2.txt")

(defun make-backup ()
  "Make a backup copy of current buffer's file.
  Create a backup of current buffer's file.
  The new file name is the old file name with trailing “~”, in the same dir.
  If such a file already exist, append more “~.
  If the current buffer is not associated with a file, its a error."
  (interactive)
  (let ((fName (buffer-file-name))
         backupName )
    (if (not fname)
        (error "current buffer is not a file." )
      (progn
        (setq backupName (concat fName "~"))
        (while (file-exists-p backupName)
          (setq backupName (concat backupName "~")))
        (copy-file fName backupName t)
        (message (concat "Backup saved as: " (file-name-nondirectory backupName)))))))

(defun my-command ()
  "One sentence summary of what this command do.

More details here. Be sure to mention the return value if relevant.
Lines here should not be longer than 70 chars,
and don't indent them."
  (interactive)
  (let (var1 var2 …)
    (setq var1 …)
    (setq var2 …)
    ;; do something …
    ))

(defun my-is-region-active ()
  "print whether region is active."
  (interactive)
  (if (use-region-p)
      (message "region active")
    (message "region not active")))

(defun my-select-line ()
  "Select current line."
  (interactive)
  (let (p1 p2)
    (setq p1 (line-beginning-position))
    (setq p2 (line-end-position))
    (goto-char p1)
    (push-mark p2)
    (setq mark-active t)))

(defun downcase-word-or-region ()
  "Downcase current word or region."
(interactive)
(let (pos1 pos2 bds)
  (if (use-region-p)
     (setq pos1 (region-beginning) pos2 (region-end))
    (progn
      (setq bds (bounds-of-thing-at-point 'symbol))
      (setq pos1 (car bds) pos2 (cdr bds))))
  ;; now, pos1 and pos2 are the starting and ending positions of the
  ;; current word, or current text selection if exist.
  (downcase-region pos1 pos2)
  ))

(defun xx ()
  "print current word."
  (interactive)
  (message "%s" (thing-at-point 'word)))

(defun my-get-boundary-and-thing ()
  "example of using `bounds-of-thing-at-point'"
  (interactive)
  (let (bounds pos1 pos2 mything)
    (setq bounds (bounds-of-thing-at-point 'symbol))
    (setq pos1 (car bounds))
    (setq pos2 (cdr bounds))
    (setq mything (buffer-substring-no-properties pos1 pos2))
    (message
     "thing begin at [%s], end at [%s], thing is [%s]"
     pos1 pos2 mything)))

(defun ff ()
  "Prompt user to enter a file name, with completion and history support."
  (interactive)
  (message "String is %s" (read-file-name "Enter file name:")))

(defun ff ()
  "Prompt user to enter a elisp regex, with input history support."
  (interactive)
  (message "Regex is %s" (read-regexp "Type a regex:")))

(defun test_ff ()
  (interactive)
  (if (y-or-n-p "Do it?")
    (progn
      ;; code to do something here
    )
  (progn
    ;; code if user answered no.
    )))

(defun ask-name (x)
  "Ask name."
  (interactive "sEnter your name: ")
  (message "Name: %s" x))

(defun ask-age (x)
  "Ask age."
  (interactive "nEnter your age: ")
  (message "Name: %d" x))

(defun print-region-boundary (x y)
  "Prints region start and end positions"
  (interactive "r")
  (message "Region begin at: %d, end at: %d" x y))

(defun do-something (x y)
  "Ask name and age"
  (interactive
   ;; complex code here that returns a list
   (list "Mary" 22))
  (message "Name is: %s, Age is: %d" x y))

(defun f (x)
  "print argument received"
  (interactive "P")
  (message "zbh test %s" x)
  ;; value of x is from universal argument, or nil if universal-argument isn't called
  )

(defun g ()
  "print `current-prefix-arg'"
  (interactive )
  (message "%s" current-prefix-arg))

(defun utest (arg1 &optional arg2 arg3)
  "Sample command to test `universal-argument'."
  (interactive
   (cond
    ((equal current-prefix-arg nil) ; no C-u
     (list 1 nil nil))
    ((equal current-prefix-arg '(4)) ; C-u
     (list 1 2 nil))
    ((equal current-prefix-arg 2) ; C-u 2
     (list 1 2 3))
    ;; more special case here

    (t ; all other cases, prompt
     (list
      (read-string "arg1:" )
      (read-string "arg2:" )
      (read-string "arg3:" )))))

  ;; now, all the parameters of your function is filled.
  ;; code body here

  (message "args are: %s %s %s" arg1 arg2 arg3)
  ;;
  )

(defun test-search ()
  (interactive)
  (let ((case-fold-search t)) ; or nil

  (goto-char (point-min))
  (while (search-forward "myStr1" nil t)
    (replace-match "myReplaceStr1"))

  (goto-char (point-min))
  (while (search-forward "myStr2" nil t)
    (replace-match "myReplaceStr2"))))

;; walk dir
(mapc
 (lambda (x) (insert x "\n"))
 (directory-files "/Users/x/em/emacs/i" nil "\.jpg$" t))

;; sample output

;; ztn_emacs_pinky_wedge_2018-02-24.jpg
;; xah_lee_photo_2018-06-28.jpg
;; xah-fly-keys_kinesis_2017-09_60363.jpg
;; todo_list_crossout_nothing.jpg
;; the_book_of_shen_lang.jpg
;; sun_type_6_keyboard_meta_compose_altgraph_keys.jpg

(defun dir-file-list ()
  (interactive)
  ;; walk dir
(mapc
 (lambda (x) (insert x "\n"))
 (directory-files "/Users/zhangbichao/Downloads" nil "\.jpg$" t)))

(global-linum-mode t)

; call a shell command
(shell-command "touch new.txt")

; call a shell command and get its output
(shell-command-to-string "ls")

; assign a list to a var
(setq mylist (list 1 "b" 3))
; prints a list
(message "%S" mylist)

; assign a list to a var
(setq mylist '(a b c))

; prints a list
(message "%S" mylist)

;; create a list of values of variables
(let ((x 3) (y 4) (z 5))
  (message "%S" (list x y z))
  ) ; prints "(3 4 5)"

;; using 3 as step
(number-sequence 0 9 3) ; (0 3 6 9)

(length '("a" "b" "c") ) ; 3

(nth 1 (list "a" "b" "c") ) ; "b"
(car (last (list "a" "b" "c")) )   ; "c"

(let ((x '(1)))
  (push 2 x)
  (equal x '(2 1)) ; true
  )
(setq mylist '("a" "b" "c"))
(pop mylist)   ; "a"
(print mylist) ; ("b" "c")

(let ((x '(1)))
  (push 2 x)
  (equal x '(2 1)) ; true
  )
(setq mylist '("a" "b" "c"))
(pop mylist)   ; "a"
(print mylist) ; ("b" "c")

;; create a hash table
(setq myHash (make-hash-table :test 'equal))
(print myHash)

(setq myHash
      #s(hash-table
         size 30
         test equal
         data (
               "joe" 3
               "jane" 9
               "liz" 5 )))

;; test
(gethash "joe" myHash )

(puthash "joe" 19 myHash)

(remhash "liz" myHash)

(gethash "jane" myHash)

(macrop 'when)

;;check if a function is defined
(fboundp 'info)
(fboundp 'setq)
(fboundp 'xyz)

;; defining a function with 2 optional params named cc and dd

(defun myfun (aa bb &optional cc dd)
  "test optional arguments"
  (insert aa bb cc dd)
  )

;; call it
(myfun "1" "2" "3"); 123
(myfun "1" "2");12
(myfun "1" "2" nil "4");

;; defining a function with rest args

(defun ff (aa bb &rest cc)
  "test rest arguments"
  (message "%s" cc) ; cc is a list
  )

;; test
(ff "1" "2" "3" "4")
;; ("3" "4")
