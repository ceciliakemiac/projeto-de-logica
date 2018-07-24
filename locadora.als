module Locadora

one sig Inventario {
	ativo: set Ativo,
	inativo: set Inativo
}

abstract sig Veiculo {
	anos: some Ano,
	roda: set Roda,
}

sig Inativo in Veiculo { }
sig Ativo in Veiculo { }

sig UmAno, DoisAnos, TresAnos, QuatroAnos, CincoAnos in Ativo { }

sig Helicoptero extends Veiculo { }
sig Motocicleta extends Veiculo { }
sig Carro extends Veiculo { }

sig Alugado in Veiculo {
	cliente: one Cliente,
	diaAlugado: some DiaAlugado,
	limpeza: one Limpeza,
	renovar: lone Renovado
}

sig Ano { }

sig Roda { 
	veiculo: one Veiculo
}

sig Cliente { 
	veiculoAlugado: some Alugado,
	inventario: one Inventario	
}

abstract sig Dia { }

sig DiaAlugado extends Dia {
	veiculo: one Veiculo
}

sig DiaLimpeza extends Dia {
	paraLimpeza: one Limpeza
}

sig Limpeza {
	dia: one DiaLimpeza,
	veiculo: one Alugado
}

sig Renovado { }

--Fatos

fact VeiculosEmLocadora {
	 all i: Inventario | all v: Veiculo | v in i.ativo or v in i.inativo
}

fact AnosDeAtividade {
	all i: Inativo | anosInativos[i]
	all a: Ativo | anosAtivos[a]

	all a: UmAno | umAnoAtivo[a]
	all a: DoisAnos | doisAnosAtivo[a]
	all a: TresAnos | tresAnosAtivo[a]
	all a: QuatroAnos | quatroAnosAtivo[a]
	all a: CincoAnos | cincoAnosAtivo[a]
}
 
fact TotalAtivo {
	UmAno + DoisAnos + TresAnos + QuatroAnos + CincoAnos = Ativo
}

fact NumeroRodas {
	all c: Carro | rodaCarro[c]
	all m: Motocicleta | rodaMotocicleta[m]
	all h: Helicoptero | rodaHelicoptero[h]
}

fact DiasAlugados {
	all v: Veiculo | #getDiasAlugados[v] <= 5
}

fact Transposicao {
	--relações que são opostas

	veiculoAlugado = ~cliente
	veiculo = ~roda
	veiculo = ~limpeza
	veiculo = ~diaAlugado
	dia = ~paraLimpeza
}

fact Limpeza {
	all l: Limpeza, a: limpeza.l | no a => no l
}

fact {
	all i: Inventario | no a: getAno[i] | no anos.a
	all i: Inventario | no n: getRenovado[i] | no renovar.n
}

--Predicados

pred anosInativos[i: Inativo] {
	#i.anos > 5
}

pred anosAtivos[a: Ativo] {
	#a.anos <= 5
}

pred umAnoAtivo[a: UmAno] {
	#a.anos = 1
}

pred doisAnosAtivo[a: DoisAnos] {
	#a.anos = 2
}

pred tresAnosAtivo[a: TresAnos] {
	#a.anos = 3
}

pred quatroAnosAtivo[a: QuatroAnos] {
	#a.anos = 4
}

pred cincoAnosAtivo[a: CincoAnos] {
	#a.anos = 5
}

pred rodaHelicoptero [h: Helicoptero] {
	#h.roda = 0
}

pred rodaMotocicleta [m: Motocicleta] {
	#m.roda = 2
}

pred rodaCarro [c: Carro] {
	#c.roda = 4
}

--Funções

fun getDiasAlugados[v: Veiculo] : set Dia {
	v.diaAlugado
}

fun getVeiculoAlugado[c: Cliente] : set Veiculo {
	c.veiculoAlugado
}

fun getAno[i: Inventario] : set Ano {
	Ano
}

fun getRenovado[i: Inventario] : set Renovado {
	Renovado
}

fun getRodas[v: Veiculo] : set Roda {
	v.roda
}

--Asserts

assert todoClienteTemVeiculo {
	all c: Cliente | #getVeiculoAlugado[c] > 0
}

assert todoVeiculoAlugadoTemDias {
	all a: Alugado | #getDiasAlugados[a] > 0
}

assert todoHelicopteroNaoTemRoda {
	all h: Helicoptero | #getRodas[h] = 0
}

check todoClienteTemVeiculo for 20
check todoVeiculoAlugadoTemDias for 20
check todoHelicopteroNaoTemRoda for 20

pred show [ ] { }

run show for 2
