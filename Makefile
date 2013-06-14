all:
	coqc mymatrices.v
	coqc syntax.v
	coqc context.v
	coqc substitution.v
	coqc typing.v
	coqc properties.v

clean:
	rm *.vo *.glob