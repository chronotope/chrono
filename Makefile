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
	awk '/^\/\/! # Chrono /{print "[Chrono][doc]",$$4}' $< > $@
	awk '/^\/\/! # Chrono /{print "[Chrono][doc]",$$4}' $< | sed 's/./=/g' >> $@
	echo >> $@
	echo '[![Chrono on Travis CI][travis-image]][travis]' >> $@
	echo '[![Chrono on Appveyor][appveyor-image]][appveyor]' >> $@
	echo '[![Chrono on crates.io][cratesio-image]][cratesio]' >> $@
	echo >> $@
	echo '[travis-image]: https://travis-ci.org/chronotope/chrono.svg?branch=master' >> $@
	echo '[travis]: https://travis-ci.org/chronotope/chrono' >> $@
	echo '[appveyor-image]: https://ci.appveyor.com/api/projects/status/2ia91ofww4w31m2w/branch/master?svg=true' >> $@
	echo '[appveyor]: https://ci.appveyor.com/project/chronotope/chrono' >> $@
	echo '[cratesio-image]: https://img.shields.io/crates/v/chrono.svg' >> $@
	echo '[cratesio]: https://crates.io/crates/chrono' >> $@
	awk '/^\/\/! # Chrono /,/^\/\/! ## /' $< | cut -b 5- | grep -v '^#' | \
		sed 's/](\.\//](https:\/\/docs.rs\/chrono\/'"$$(cargo pkgid | cut -d: -f3)"'\/chrono\//g' >> $@
	echo '***[Complete Documentation][doc]***' >> $@
	echo >> $@
	echo '[doc]: https://docs.rs/chrono/'"$$(cargo pkgid | cut -d: -f3)"'/' >> $@
	echo >> $@
	awk '/^\/\/! ## /,!/^\/\/!/' $< | cut -b 5- | grep -v '^# ' | \
		sed 's/](\.\//](https:\/\/docs.rs\/chrono\/'"$$(cargo pkgid | cut -d: -f3)"'\/chrono\//g' >> $@

.PHONY: test
test:
	cargo test --features 'serde rustc-serialize bincode'

.PHONY: doc
doc: authors readme
	cargo doc --features 'serde rustc-serialize bincode'

.PHONY: doc-publish
doc-publish: doc
	( \
		PKGID="$$(cargo pkgid)"; \
		PKGNAMEVER="$${PKGID#*#}"; \
		PKGNAME="$${PKGNAMEVER%:*}"; \
		REMOTE="$$(git config --get remote.origin.url)"; \
		cd target/doc && \
		rm -rf .git && \
		git init && \
		git checkout --orphan gh-pages && \
		echo '<!doctype html><html><head><meta http-equiv="refresh" content="0;URL='$$PKGNAME'/index.html"></head><body></body></html>' > index.html && \
		git add . && \
		git commit -m 'updated docs.' && \
		git push "$$REMOTE" gh-pages -f; \
	)

