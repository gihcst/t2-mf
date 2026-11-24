// Integrantes: Giovanna Cruz Castro, Eduarda dos Santos Patricio

class DequeCircular {
  // --- Representação Concreta (Fila Circular Clássica com Head e Tail) ---
  var arr: array<int>
  var head: int // Índice do primeiro elemento
  var tail: int // Índice da próxima posição livre no final

  // --- Representação Abstrata (Ghost) ---
  ghost var Conteudo: seq<int>
  ghost var Repr: set<object>
  ghost var CapacidadeMax: int

  // Função auxiliar linear para mapear índice lógico -> índice circular no array (evita '%' / timeout)
  ghost function Indice(i: int): int
    reads this
    requires arr.Length > 0
    requires 0 <= head < arr.Length
    requires 0 <= i < arr.Length
  {
    if head + i < arr.Length then head + i
    else head + i - arr.Length
  }

  // Função auxiliar ghost para calcular a quantidade de elementos a partir de head e tail
  ghost function TamanhoLogico(): int
    reads this, arr
    requires arr.Length > 0
    requires 0 <= head < arr.Length && 0 <= tail < arr.Length
  {
    if tail >= head then tail - head
    else arr.Length - head + tail
  }

  // --- Invariante de Classe ---
  ghost predicate Valid()
    reads this, Repr
  {
    this in Repr &&
    arr in Repr &&
    arr.Length >= 2 && // Capacidade mínima 1 + 1 posição sentinela
    CapacidadeMax == arr.Length - 1 &&
    CapacidadeMax > 0 &&
    0 <= head < arr.Length &&
    0 <= tail < arr.Length &&
    |Conteudo| == TamanhoLogico() &&
    |Conteudo| <= arr.Length - 1 &&
    forall i :: 0 <= i < |Conteudo| ==> Conteudo[i] == arr[Indice(i)]
  }

  // --- Construtor ---
  constructor (capacidade: int)
    requires capacidade > 0
    ensures Valid()
    ensures fresh(Repr)
    ensures Conteudo == []
    ensures Capacidade() == capacidade
  {
    arr := new int[capacidade + 1]; // +1 posição sentinela para distinguir vazio de cheio
    head := 0;
    tail := 0;
    Conteudo := [];
    Repr := {this, arr};
    CapacidadeMax := capacidade;
  }

  // --- Operações de Consulta ---
  function Capacidade(): int
    reads this, Repr
    requires Valid()
    ensures Capacidade() == CapacidadeMax
  {
    arr.Length - 1
  }

  function Tamanho(): int
    reads this, Repr
    requires Valid()
    ensures Tamanho() == |Conteudo|
  {
    if tail >= head then tail - head
    else arr.Length - head + tail
  }

  function EstaVazio(): bool
    reads this, Repr
    requires Valid()
    ensures EstaVazio() <==> |Conteudo| == 0
  {
    head == tail
  }

  function EstaCheio(): bool
    reads this, Repr
    requires Valid()
    ensures EstaCheio() <==> |Conteudo| == Capacidade()
  {
    (if tail + 1 < arr.Length then tail + 1 else 0) == head
  }

  method Contem(x: int) returns (encontrado: bool)
    requires Valid()
    ensures encontrado <==> x in Conteudo
  {
    var n := Tamanho();
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant forall j :: 0 <= j < i ==> Conteudo[j] != x
      decreases n - i
    {
      var idx := if head + i < arr.Length then head + i else head + i - arr.Length;
      if arr[idx] == x {
        assert Conteudo[i] == x;
        return true;
      }
      i := i + 1;
    }
    return false;
  }

  // --- Operações de Inserção e Remoção ---
  method AdicionarFim(x: int)
    requires Valid()
    requires !EstaCheio()
    modifies Repr
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    ensures Capacidade() == old(Capacidade())
    ensures Conteudo == old(Conteudo) + [x]
  {
    arr[tail] := x;
    tail := if tail + 1 < arr.Length then tail + 1 else 0;
    Conteudo := Conteudo + [x];
  }

  method AdicionarInicio(x: int)
    requires Valid()
    requires !EstaCheio()
    modifies Repr
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    ensures Capacidade() == old(Capacidade())
    ensures Conteudo == [x] + old(Conteudo)
  {
    var oldHead := head;
    var oldConteudo := Conteudo;
    var novoHead := if head > 0 then head - 1 else arr.Length - 1;
    head := novoHead;
    arr[head] := x;
    Conteudo := [x] + Conteudo;

    // Prova construtiva linear para cada posição i do novo Conteudo
    forall i | 0 <= i < |Conteudo|
      ensures Conteudo[i] == arr[Indice(i)]
    {
      if i == 0 {
        assert Indice(0) == head;
      } else {
        var oldIdx := if oldHead + (i - 1) < arr.Length then oldHead + (i - 1) else oldHead + (i - 1) - arr.Length;
        assert Indice(i) == oldIdx;
        assert oldConteudo[i - 1] == arr[oldIdx];
      }
    }
  }

  method RemoverInicio() returns (x: int)
    requires Valid()
    requires !EstaVazio()
    modifies Repr
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    ensures Capacidade() == old(Capacidade())
    ensures x == old(Conteudo)[0]
    ensures Conteudo == old(Conteudo)[1..]
  {
    x := arr[head];
    head := if head + 1 < arr.Length then head + 1 else 0;
    Conteudo := Conteudo[1..];
  }

  method RemoverFim() returns (x: int)
    requires Valid()
    requires !EstaVazio()
    modifies Repr
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    ensures Capacidade() == old(Capacidade())
    ensures x == old(Conteudo)[|old(Conteudo)| - 1]
    ensures Conteudo == old(Conteudo)[..|old(Conteudo)| - 1]
  {
    var novoTail := if tail > 0 then tail - 1 else arr.Length - 1;
    tail := novoTail;
    x := arr[tail];
    Conteudo := Conteudo[..|Conteudo| - 1];
  }

  // --- Operação de Redimensionamento ---
  method Redimensionar(novaCapacidade: int)
    requires Valid()
    requires novaCapacidade > Capacidade()
    modifies Repr
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    ensures Capacidade() == novaCapacidade
    ensures Conteudo == old(Conteudo)
  {
    var n := Tamanho();
    var oldArr := arr;
    var oldHead := head;
    var oldConteudo := Conteudo;
    var novoArr := new int[novaCapacidade + 1];
    var i := 0;

    while i < n
      modifies novoArr
      invariant Conteudo == oldConteudo
      invariant 0 <= i <= n
      invariant forall k :: 0 <= k < i ==> novoArr[k] == oldConteudo[k]
      decreases n - i
    {
      var idx := if oldHead + i < oldArr.Length then oldHead + i else oldHead + i - oldArr.Length;
      assert oldConteudo[i] == oldArr[idx];
      novoArr[i] := oldArr[idx];
      i := i + 1;
    }

    arr := novoArr;
    head := 0;
    tail := n;
    Repr := {this, arr};
    CapacidadeMax := novaCapacidade;
  }
}

// --- Método Main com Testes Unitários ---
method Main() {
  var dq := new DequeCircular(3);
  assert dq.EstaVazio();
  assert !dq.EstaCheio();
  assert dq.Tamanho() == 0;
  assert dq.Capacidade() == 3;
  assert dq.Conteudo == [];
  var temVazio := dq.Contem(10);
  assert !temVazio;

  // Inserções no fim e no início (forçando circularidade do índice head)
  dq.AdicionarFim(10);
  assert dq.Conteudo == [10];

  dq.AdicionarInicio(5);
  assert dq.Conteudo == [5, 10];

  dq.AdicionarFim(20);
  assert dq.Conteudo == [5, 10, 20];
  assert dq.EstaCheio();
  assert dq.Tamanho() == 3;

  // Busca de elementos
  var tem5 := dq.Contem(5);
  assert tem5;
  var tem10 := dq.Contem(10);
  assert tem10;
  var tem20 := dq.Contem(20);
  assert tem20;
  var tem99 := dq.Contem(99);
  assert !tem99;

  // Redimensionamento com o array circular "quebrado" (head > tail)
  dq.Redimensionar(5);
  assert dq.Capacidade() == 5;
  assert dq.Tamanho() == 3;
  assert dq.Conteudo == [5, 10, 20];
  assert !dq.EstaCheio();

  // Novas inserções após redimensionar
  dq.AdicionarInicio(1);
  dq.AdicionarFim(30);
  assert dq.Conteudo == [1, 5, 10, 20, 30];
  assert dq.EstaCheio();
  assert dq.Tamanho() == 5;

  // Remoções nas duas extremidades até esvaziar completamente
  var r1 := dq.RemoverInicio();
  assert r1 == 1;
  var r2 := dq.RemoverFim();
  assert r2 == 30;
  assert dq.Conteudo == [5, 10, 20];

  var r3 := dq.RemoverInicio();
  assert r3 == 5;
  var r4 := dq.RemoverFim();
  assert r4 == 20;
  var r5 := dq.RemoverInicio();
  assert r5 == 10;

  assert dq.EstaVazio();
  assert dq.Tamanho() == 0;
  assert dq.Conteudo == [];

  print "Todos os testes passaram bonitinho!\n";
}