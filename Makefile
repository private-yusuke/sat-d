sat-d:
	dub build -b release

test: sat-d
	./test.sh

clean:
	rm -f sat-d