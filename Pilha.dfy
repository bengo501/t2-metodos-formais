// =============================================================================
//  Métodos Formais para Computação  -  Trabalho T2
//  Prof. Júlio Machado  -  PUCRS / Bacharelado em Ciência da Computação
//
//  Tipo Abstrato de Dados: PILHA (Stack) sem limite de tamanho,
//  com implementação concreta baseada em arrays.
//
//  Integrantes do grupo:
//    - Bernardo Klein
//    - Giovana Raupp
// =============================================================================

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
  //  inverter()  -  RETORNA uma NOVA pilha com a ordem invertida.
  //  NÃO altera esta pilha (sem mutação).
  method inverter() returns (rev: Pilha)
    requires Valid()
    ensures rev.Valid() && fresh(rev.Repr)
    ensures unchanged(this)                      // esta pilha permanece intacta
    ensures |rev.elementos| == |elementos|
    ensures forall k :: 0 <= k < |elementos| ==>
              rev.elementos[k] == elementos[|elementos| - 1 - k]
  {
    var n := tamPilha;
    var novo := new int[n];
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant n == tamPilha
      invariant n <= dados.Length
      invariant novo.Length == n
      invariant forall k :: 0 <= k < i ==> novo[k] == dados[n - 1 - k]
      modifies novo
      decreases n - i
    {
      novo[i] := dados[n - 1 - i];
      i := i + 1;
    }
    // a nova pilha recebe o array já invertido
    rev := new Pilha();
    rev.dados := novo;
    rev.tamPilha := n;
    rev.elementos := novo[..n];
    rev.Repr := {rev, novo};
  }

  // =========================================================================
  //  empilharSobre(outra)  -  RETORNA uma NOVA pilha resultante de empilhar
  //  `outra` SOBRE esta pilha (esta embaixo, `outra` em cima; o topo de `outra`
  //  vira o topo do resultado). NÃO altera nenhuma das duas pilhas.
  //      nova.elementos == this.elementos + outra.elementos
  method empilharSobre(outra: Pilha) returns (nova: Pilha)
    requires Valid() && outra.Valid()
    ensures nova.Valid() && fresh(nova.Repr)
    ensures nova.elementos == elementos + outra.elementos
    ensures unchanged(this) && unchanged(outra)  // operandos intactos
  {
    var total := tamPilha + outra.tamPilha;
    var novo := new int[total];

    // copia os elementos desta pilha (base)
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

    assert novo[..tamPilha] == dados[..tamPilha];
    assert novo[tamPilha..total] == outra.dados[..outra.tamPilha];
    assert novo[..total] == novo[..tamPilha] + novo[tamPilha..total];

    nova := new Pilha();
    nova.dados := novo;
    nova.tamPilha := total;
    nova.elementos := dados[..tamPilha] + outra.dados[..outra.tamPilha];
    nova.Repr := {nova, novo};
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

  // ---- inverter: retorna NOVA pilha, sem alterar a original ----
  var pInv := p.inverter();
  assert p.elementos == [10, 20, 40];      // original permanece intacta
  assert pInv.elementos == [40, 20, 10];   // nova, invertida
  assert pInv.topo() == 10;
  assert pInv.tamanho() == 3;

  // ---- empilhar uma pilha sobre outra: retorna NOVA, sem alterar nenhuma ----
  var q := new Pilha();
  q.empilhar(1);
  q.empilhar(2);
  assert q.elementos == [1, 2];

  // base = pInv = [40,20,10] ; topo = q = [1,2]  =>  nova == [40,20,10,1,2]
  var r := pInv.empilharSobre(q);
  assert pInv.elementos == [40, 20, 10];   // operando intacto
  assert q.elementos == [1, 2];            // operando intacto
  assert r.elementos == [40, 20, 10, 1, 2];
  assert r.tamanho() == 5;
  assert r.topo() == 2;

  // ---- desempilhando a nova pilha recuperamos a ordem esperada ----
  var a1 := r.desempilhar();   // 2
  assert a1 == 2 && r.elementos == [40, 20, 10, 1];
  var a2 := r.desempilhar();   // 1
  assert a2 == 1 && r.elementos == [40, 20, 10];
  var a3 := r.desempilhar();   // 10
  assert a3 == 10 && r.elementos == [40, 20];
  var a4 := r.desempilhar();   // 20
  assert a4 == 20 && r.elementos == [40];
  var a5 := r.desempilhar();   // 40
  assert a5 == 40 && r.elementos == [];
  assert [a1, a2, a3, a4, a5] == [2, 1, 10, 20, 40];
  assert r.vazia();

  print "Pilha: todas as assercoes foram verificadas estaticamente com sucesso.\n";
}
