class Stack{

    ghost var s:seq<int>;

    // Abstract state
    function AbsInv(): bool {true}

    // Concrete state
    var a:array<int>;
    var size:int;

    function RepInv(): bool
    reads `size, `a
    {
        0 <= size <= a.Length
    }

    function Sound():bool
    reads this, a
    {
        AbsInv() && 
        RepInv() && 
        size == |s| && forall k :: 0 <= k < size ==> s[k] == a[k]
    }

    
    // ADT Code && Spec


    function Empty(): bool
    reads `s
    {
        s == []
    }

    constructor()
    ensures Sound() && Empty()
    {
        a := new int[10];
        size := 0;
        s := [];
    }

    method push(x: int)
    requires Sound() 
    ensures Sound() && s == old(s) + [x]
    modifies `a, a, `size, `s
    {
        resize();

        a[size] := x;
        size := size + 1;
        s := s + [x];
    }

    method resize()
    requires Sound()
    ensures Sound()
    ensures size < a.Length
    modifies `a
    {
        if( size == a.Length) {
            var b := new int[a.Length*2+1];
            var i := 0;
            while i < size
            decreases size - i
            invariant 0 <= i <= size
            invariant forall k :: 0 <= k < i ==> s[k] == b[k]
            modifies b
            {
                b[i] := a[i];
                i := i +1;
            }
            a := b;
        }
    }
    

    method pop() returns (x: int)
    requires AbsInv() && !Empty()
    // ambos a mesma coisa mas o segundo muito mais simples
    //ensures RepInv() && s == old(s)[0..|s|-1] && x == old(s)[|old(s)|-1]
    ensures AbsInv() && s + [x] == old(s)

    static method main(){
        var stack:Stack := new Stack();

        stack.push(0);
        var v0 := stack.pop();

        stack.push(1);
        stack.push(2);

        var v1 := stack.pop();
        var v2 := stack.pop();
        assert stack.s == [];
        assert v1 == 2 && v2 == 1;

       
    }
}