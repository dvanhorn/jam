runall:
	for x in `find .  -name '*.rkt'`; do racket $$x; done
