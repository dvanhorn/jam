RKTS = $(wildcard *.rkt)
OBJS = $(patsubst %.rkt,%,$(RKTS))

testall:
	for x in $(OBJS); do \
	racket -e "(begin (require \"$$x.rkt\") ($$x))"; \
	done

test:
	mkdir test
	for x in $(OBJS); do \
	echo "#lang racket/base (require \"../$$x.rkt\") ($$x)" > test/$$x.rkt; \
	done

runall:
	for x in `find .  -name '*.rkt'`; do racket $$x; done

