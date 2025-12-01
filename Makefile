default: all

all: 
	agda Everything.agda

time:
	time agda Everything.agda

clean:
	git clean -fx
