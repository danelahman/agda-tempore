default: all

all: 
	agda Everything.agda

time:
	time agda Everything.agda

examples:
	agda TypeInference/Examples.agda

clean:
	git clean -fx
