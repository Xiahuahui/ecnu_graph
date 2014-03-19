package dot

import "testing"

func Test_Convert(test *testing.T) {
	result := convert("testgraph.json", "testgraph.003")
	sc := `digraph testgraph003 {
	S -> A [label=100]
	S -> B [label=6]
	S -> B [label=14]
	S -> C [label=200]
	A -> S [label=15]
	A -> B [label=5]
	A -> D [label=20]
	A -> T [label=44]
	B -> S [label=14]
	B -> A [label=5]
	B -> D [label=30]
	B -> E [label=18]
	C -> S [label=9]
	C -> E [label=24]
	D -> A [label=20]
	D -> B [label=30]
	D -> E [label=2]
	D -> F [label=11]
	D -> T [label=16]
	E -> B [label=18]
	E -> C [label=24]
	E -> D [label=2]
	E -> F [label=6]
	E -> T [label=19]
	F -> D [label=11]
	F -> E [label=6]
	F -> T [label=6]
	T -> A [label=44]
	T -> D [label=16]
	T -> F [label=6]
	T -> E [label=19]
}`
	if result != sc {
		test.Errorf("Result and sc should be same but\n%v\n\n%v", result, sc)
	}
}