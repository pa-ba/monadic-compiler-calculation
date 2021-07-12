default: 
	agda Everything.agda

clean:
	find . -type f -name '*.agdai' -delete
