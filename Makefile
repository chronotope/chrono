.PHONY: all
all:
	@echo 'Try `cargo build` instead.'

.PHONY: authors
authors:
	echo 'Chrono is mainly written by Kang Seonghoon <public+rust@mearie.org>,' > AUTHORS.txt
	echo 'and also the following people (in ascending order):' >> AUTHORS.txt
	echo >> AUTHORS.txt
	git log --format='%aN <%aE>' | grep -v 'Kang Seonghoon' | sort -u >> AUTHORS.txt

