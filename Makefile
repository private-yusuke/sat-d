sat-d:
	dub build -b debug

test: sat-d
	./test.sh

clean:
	rm -f sat-d