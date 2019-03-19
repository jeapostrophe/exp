.PHONY: upload

workout2: upload

upload: index.html
	rsync -aL --delete-after --progress index.html imgs style.css uml:public_html/w/

index.html: workout2.rkt
	racket -t $^ > $@
