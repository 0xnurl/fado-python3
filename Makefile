install: build
	sudo python setup.py install

build:
	python setup.py build_ext --inplace	

uninstall:
	sudo python setup.py install --record .manifest.txt
	for i in $$(less .manifest.txt); do sudo rm -f $$i; done
	sudo rm .manifest.txt

