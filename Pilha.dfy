class Pilha {
  // ------------------------- Representação concreta 
  var dados: array<int>   // array de apoio que armazena os elementos
  var tamPilha: int       // nº de elementos em uso (topo em dados[tamPilha-1])

  // -------------------- Representação abstrata (ghost) 
  ghost var elementos: seq<int>   // coleção abstrata de elementos da pilha
  ghost var Repr: set<object>     // conjunto de objetos que compõem a pilha
                                  // (informação necessária para o framing)

  // --------------------------- Invariante de classe 
  // Predicado que amarra a representação concreta (array + contador) à
  // representação abstrata (sequência `elementos`).
  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {
    this in Repr &&
    dados in Repr &&
    0 <= tamPilha <= dados.Length &&
    elementos == dados[..tamPilha]
  }

  // =========================================================================
  //  CONSTRUTOR  -  cria uma pilha vazia
  constructor ()
    ensures Valid() && fresh(Repr)
    ensures elementos == []
  {
    dados := new int[0];
    tamPilha := 0;
    elementos := [];
    Repr := {this, dados};
  }

  // =========================================================================
  //  vazia()  -  consulta se a pilha está vazia
  predicate vazia()
    requires Valid()
    reads this, Repr
    ensures vazia() <==> |elementos| == 0
  {
    tamPilha == 0
  }

  // =========================================================================
  //  tamanho()  -  nº de elementos armazenados
  function tamanho(): int
    requires Valid()
    reads this, Repr
    ensures tamanho() == |elementos|
  {
    tamPilha
  }

  // =========================================================================
  //  topo()  -  lê o valor do topo SEM removê-lo (pilha não vazia)
  function topo(): int
    requires Valid()
    requires |elementos| > 0
    reads this, Repr
    ensures topo() == elementos[|elementos| - 1]
  {
    dados[tamPilha - 1]
  }

  // =========================================================================
  //  aumentarCapacidade()  -  método auxiliar: realoca `dados` num array maior
  //  (garante que a pilha não tenha limite de tamanho)
  method aumentarCapacidade()
    requires Valid()
    requires tamPilha == dados.Length
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures elementos == old(elementos)
    ensures tamPilha == old(tamPilha)
    ensures dados.Length > old(dados.Length)
  {
    ghost var s := elementos;             // == dados[..tamPilha] (Valid de entrada)
    var novaCap := if dados.Length == 0 then 1 else 2 * dados.Length;
    var novo := new int[novaCap];
    var i := 0;
    while i < tamPilha
      invariant 0 <= i <= tamPilha
      invariant tamPilha <= dados.Length
      invariant tamPilha <= novo.Length
      invariant forall k :: 0 <= k < i ==> novo[k] == dados[k]
      modifies novo
      decreases tamPilha - i
    {
      novo[i] := dados[i];
      i := i + 1;
    }
    assert dados[..tamPilha] == s;        // s == elementos == dados[..tamPilha]
    assert novo[..tamPilha] == s;         // por extensionalidade de sequências
    dados := novo;
    Repr := {this, dados};
  }

  // =========================================================================
  //  empilhar(x)  -  adiciona um novo elemento no TOPO da pilha
  method empilhar(x: int)
    requires Valid()
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures elementos == old(elementos) + [x]
  {
    if tamPilha == dados.Length {
      aumentarCapacidade();
    }
    dados[tamPilha] := x;
    tamPilha := tamPilha + 1;
    elementos := elementos + [x];
  }

  // =========================================================================
  //  desempilhar()  -  remove e devolve o elemento do TOPO (pilha não vazia)
  method desempilhar() returns (x: int)
    requires Valid()
    requires |elementos| > 0
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures x == old(elementos)[|old(elementos)| - 1]
    ensures elementos == old(elementos)[..|old(elementos)| - 1]
    ensures old(elementos) == elementos + [x]
  {
    x := dados[tamPilha - 1];
    tamPilha := tamPilha - 1;
    elementos := elementos[..|elementos| - 1];
  }

  // =========================================================================
  //  inverter()  -  inverte a ordem dos elementos da pilha (in-place)
  method inverter()
    requires Valid()
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures |elementos| == |old(elementos)|
    ensures forall k :: 0 <= k < |elementos| ==>
              elementos[k] == old(elementos)[|old(elementos)| - 1 - k]
  {
    ghost var s := elementos;   // == old(elementos) == dados[..tamPilha]
    var i := 0;
    var j := tamPilha - 1;
    while i < j
      invariant 0 <= i <= tamPilha
      invariant -1 <= j < tamPilha
      invariant i + j == tamPilha - 1
      invariant tamPilha == |s|
      invariant this in Repr && dados in Repr
      invariant 0 <= tamPilha <= dados.Length
      // pontas já invertidas:
      invariant forall k :: 0 <= k < i ==> dados[k] == s[tamPilha - 1 - k]
      invariant forall k :: j < k < tamPilha ==> dados[k] == s[tamPilha - 1 - k]
      // miolo ainda na ordem original:
      invariant forall k :: i <= k <= j ==> dados[k] == s[k]
      modifies dados
      decreases j - i
    {
      dados[i], dados[j] := dados[j], dados[i];
      i := i + 1;
      j := j - 1;
    }
    elementos := dados[..tamPilha];
  }

  // =========================================================================
  //  empilharSobre(outra)  -  empilha a pilha `outra` SOBRE esta pilha.
  //  Os elementos de `outra` são colocados no topo desta, preservando a ordem
  //  interna de `outra` (o topo de `outra` torna-se o novo topo do resultado).
  //  A pilha `outra` permanece inalterada.
  //      resultado.elementos == this.elementos ++ outra.elementos

  method empilharSobre(outra: Pilha)
    requires Valid() && outra.Valid()
    requires outra != this
    requires Repr !! outra.Repr        // pilhas disjuntas (sem aliasing)
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures elementos == old(elementos) + outra.elementos
    ensures unchanged(outra)           // `outra` não é modificada
    ensures outra.Valid()
  {
    ghost var s1 := elementos;          // == dados[..tamPilha]
    ghost var s2 := outra.elementos;    // == outra.dados[..outra.tamPilha]
    var total := tamPilha + outra.tamPilha;
    var novo := new int[total];

    // copia os elementos desta pilha
    var k := 0;
    while k < tamPilha
      invariant 0 <= k <= tamPilha
      invariant tamPilha <= dados.Length
      invariant novo.Length == total
      invariant forall t :: 0 <= t < k ==> novo[t] == dados[t]
      modifies novo
      decreases tamPilha - k
    {
      novo[k] := dados[k];
      k := k + 1;
    }

    // copia, em cima, os elementos da pilha `outra`
    var m := 0;
    while m < outra.tamPilha
      invariant 0 <= m <= outra.tamPilha
      invariant outra.tamPilha <= outra.dados.Length
      invariant novo.Length == total
      invariant forall t :: 0 <= t < tamPilha ==> novo[t] == dados[t]
      invariant forall t :: 0 <= t < m ==> novo[tamPilha + t] == outra.dados[t]
      modifies novo
      decreases outra.tamPilha - m
    {
      novo[tamPilha + m] := outra.dados[m];
      m := m + 1;
    }

    assert novo[..tamPilha] == s1;
    assert novo[tamPilha..total] == s2;
    assert novo[..total] == novo[..tamPilha] + novo[tamPilha..total];

    dados := novo;
    tamPilha := total;
    elementos := s1 + s2;
    Repr := {this, dados};
  }
}

// =============================================================================
//  MÉTODO Main  -  demonstração de uso + testes (estilo teste unitário) cuja
//  corretude é VERIFICADA estaticamente pelo Dafny através de assert.

method Main()
{
  // ---- pilha recém-criada está vazia ----
  var p := new Pilha();
  assert p.vazia();
  assert p.tamanho() == 0;
  assert p.elementos == [];

  // ---- empilhar ----
  p.empilhar(10);
  p.empilhar(20);
  p.empilhar(30);
  assert !p.vazia();
  assert p.tamanho() == 3;
  assert p.topo() == 30;
  assert p.elementos == [10, 20, 30];

  // ---- desempilhar (remove o topo) ----
  var x := p.desempilhar();
  assert x == 30;
  assert p.topo() == 20;
  assert p.tamanho() == 2;
  assert p.elementos == [10, 20];

  // ---- topo() não remove ----
  var t := p.topo();
  assert t == 20;
  assert p.tamanho() == 2;

  p.empilhar(40);
  assert p.elementos == [10, 20, 40];

  // ---- inverter ----
  p.inverter();
  assert p.elementos == [40, 20, 10];
  assert p.topo() == 10;

  // ---- empilhar uma pilha sobre outra ----
  var q := new Pilha();
  q.empilhar(1);
  q.empilhar(2);
  assert q.elementos == [1, 2];

  // p = [40,20,10] ; q = [1,2]  =>  p.empilharSobre(q) == [40,20,10,1,2]
  p.empilharSobre(q);
  assert p.elementos == [40, 20, 10, 1, 2];
  assert p.tamanho() == 5;
  assert p.topo() == 2;
  assert q.elementos == [1, 2];     // `q` permanece inalterada

  // ---- desempilhando tudo, recuperamos a ordem esperada ----
  var a1 := p.desempilhar();   // 2
  assert a1 == 2 && p.elementos == [40, 20, 10, 1];
  var a2 := p.desempilhar();   // 1
  assert a2 == 1 && p.elementos == [40, 20, 10];
  var a3 := p.desempilhar();   // 10
  assert a3 == 10 && p.elementos == [40, 20];
  var a4 := p.desempilhar();   // 20
  assert a4 == 20 && p.elementos == [40];
  var a5 := p.desempilhar();   // 40
  assert a5 == 40 && p.elementos == [];
  assert [a1, a2, a3, a4, a5] == [2, 1, 10, 20, 40];
  assert p.vazia();

  print "Pilha: todas as assercoes foram verificadas estaticamente com sucesso.\n";
}
