# this Makefile is mostly for the packaging convenience.
# casual users should use `cargo` to retrieve the appropriate version of Chrono.

.PHONY: all
all:
	@echo 'Try `cargo build` instead.'

.PHONY: authors
authors:
	echo 'Chrono is mainly written by Kang Seonghoon <public+rust@mearie.org>,' > AUTHORS.txt
	echo 'and also the following people (in ascending order):' >> AUTHORS.txt
	echo >> AUTHORS.txt
	git log --format='%aN <%aE>' | grep -v 'Kang Seonghoon' | sort -u >> AUTHORS.txt

.PHONY: readme
readme: README.md

README.md: src/lib.rs
	# really, really sorry for this mess.
	( \
		VERSION="$$(cargo pkgid | cut -d: -f3)"; \
		awk '/^\/\/! # Chrono /{print "[Chrono][docsrs]",$$4}' $<; \
		awk '/^\/\/! # Chrono /{print "[Chrono][docsrs]",$$4}' $< | sed 's/./=/g'; \
		echo; \
		echo '[![Chrono on Travis CI][travis-image]][travis]'; \
		echo '[![Chrono on Appveyor][appveyor-image]][appveyor]'; \
		echo '[![Chrono on crates.io][cratesio-image]][cratesio]'; \
		echo '[![Chrono on docs.rs][docsrs-image]][docsrs]'; \
		echo; \
		echo '[travis-image]: https://travis-ci.org/chronotope/chrono.svg?branch=master'; \
		echo '[travis]: https://travis-ci.org/chronotope/chrono'; \
		echo '[appveyor-image]: https://ci.appveyor.com/api/projects/status/2ia91ofww4w31m2w/branch/master?svg=true'; \
		echo '[appveyor]: https://ci.appveyor.com/project/chronotope/chrono'; \
		echo '[cratesio-image]: https://img.shields.io/crates/v/chrono.svg'; \
		echo '[cratesio]: https://crates.io/crates/chrono'; \
		echo '[docsrs-image]: https://docs.rs/chrono/badge.svg?version='$$VERSION; \
		echo '[docsrs]: https://docs.rs/chrono/'$$VERSION'/'; \
		echo; \
		awk '/^\/\/! # Chrono /,/^\/\/! ## /' $< | cut -b 5- | grep -v '^#' | \
			sed 's/](\.\//](https:\/\/docs.rs\/chrono\/'$$VERSION'\/chrono\//g'; \
		echo; \
		awk '/^\/\/! ## /,!/^\/\/!/' $< | cut -b 5- | grep -v '^# ' | \
			sed 's/](\.\//](https:\/\/docs.rs\/chrono\/'$$VERSION'\/chrono\//g' \
	) > $@

.PHONY: test
test:
	TZ=UTC0 cargo test --features 'serde rustc-serialize bincode' --lib
	TZ=ACST-9:30 cargo test --features 'serde rustc-serialize bincode' --lib
	TZ=EST4 cargo test --features 'serde rustc-serialize bincode'

.PHONY: doc
doc: authors readme
	cargo doc --features 'serde rustc-serialize bincode'

