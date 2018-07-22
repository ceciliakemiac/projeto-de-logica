module Locadora

one sig Inventario {
	veiculo: set Veiculo
}

abstract sig Veiculo {
	anos: some Ano,
	roda: set Roda,
}

sig Inativo extends Veiculo { }
sig Ativo extends Veiculo { }

sig Helicoptero in Veiculo { }
sig Motocicleta in Veiculo { }
sig Carro in Veiculo { }

sig Alugado in Veiculo {
	cliente: one Cliente,
	diaAlugado: some Dia,
	limpeza: one Limpeza,
	renovar: lone Renovado
}

sig Ano { }

sig Roda { }

sig Cliente { 
	veiculoAlugado: some Alugado	
}

sig Dia { }

one sig Limpeza {
	dia: one Dia
}

sig Renovado { }

---------------------------------Fatos-------------------------------

fact VeiculosEmLocadora {
	all i: Inventario | all v: Veiculo | v in i.veiculo
}

fact AnosDeAtividade {
	all i: Inativo | anosInativos[i]
	all a: Ativo | anosAtivos[a]
}
 
fact TotalVeiculo {
	Helicoptero + Motocicleta + Carro = Veiculo
}

fact NumeroRodas {
	all c: Carro | rodaCarro[c]
	all m: Motocicleta | rodaMotocicleta[m]
	all h: Helicoptero | rodaHelicoptero[h]
}

fact DiasAlugados {
	all v: Veiculo | #getDiasAlugados[v] <= 5
	all v: Veiculo | veiculoAlugadoTemDias[v]

	one i: Inventario | all a: getAlugado[i] | no a.cliente => no a.diaAlugado
}

fact Aluguel {
	veiculoAlugado = ~cliente
}

fact {
	no r: Roda | no roda.r
	no d: Dia | no diaAlugado.d
	no a: Ano | no anos.a
	no l: Limpeza | no limpeza.l
	no n: Renovado | no renovar.n
}

---------------------------------------------------------------------

pred anosInativos[i: Inativo] {
	#i.anos > 5
}

pred anosAtivos[a: Ativo] {
	#a.anos <= 5
}

pred umAnoAtivo[a: Ativo] {
	#a.anos = 1
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

pred veiculoAlugadoTemDias[a: Alugado] {
	(#getCliente[a] > 0) => (#getDiasAlugados[a] > 0)
}

--------------------------------------Funcao---------------------------------------

fun getDiasAlugados[v: Veiculo] : set Dia {
	v.diaAlugado
}

fun getCliente[v: Veiculo] : lone Cliente {
	v.cliente
}

fun getAlugado[i: Inventario] : set Alugado {
	Alugado
}

fun getVeiculoAlugado[c: Cliente] : set Veiculo {
	c.veiculoAlugado
}

------------------------------------Assert----------------------------------------

assert todoClienteTemVeiculo {
	all c: Cliente | #getVeiculoAlugado[c] > 0
}

assert todoVeiculoAlugadoTemDias {
	all a: Alugado | #getDiasAlugados[a] > 0
}


check todoClienteTemVeiculo for 20
check todoVeiculoAlugadoTemDias for 20

pred show [ ] { }

run show for 3
