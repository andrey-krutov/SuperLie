(* Wolfram Language Test file *)

CartanMatrixAlgebra[g, {x,h,y}, {{2,-1},{-1,2}}]

Test[
	Dim[g]
	,
	8
	,
	TestID->"Dim sl(2) from Cartan matrix"
]
