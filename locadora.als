module Locadora

one sig Locadora {
	veiculo: set Veiculo
}

abstract sig Veiculo {
	anos: some Ano,
	roda: set Roda,
	cliente: lone Cliente,
	diaAlugado: set Dia
}

sig Inativo extends Veiculo { }
sig Ativo extends Veiculo { }

sig Helicoptero in Veiculo { }
sig Motocicleta in Veiculo { }
sig Carro in Veiculo { }

sig Ano { }

sig Roda { }

sig Cliente { 
	veiculoAlugado: some Veiculo	
}

sig Dia { }

---------------------------------Fatos-------------------------------

fact VeiculosEmLocadora {
	one l: Locadora | all v: Veiculo | v in l.veiculo
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
}

fact Aluguel {
	veiculoAlugado = ~cliente
}

fact SemDiasSeNaoAlugado {
	all v: Veiculo | no v.cliente => no v.diaAlugado
}

fact {
	no r: Roda | no roda.r
	no d: Dia | no diaAlugado.d
	no a: Ano | no anos.a
}

---------------------------------------------------------------------

pred anosInativos[i: Inativo] {
	#i.anos > 5
}

pred anosAtivos[a: Ativo] {
	#a.anos <= 5
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

pred veiculoAlugadoTemDias[v: Veiculo] {
	(#getCliente[v] > 0) => (#getDiasAlugados[v] > 0)
}

--------------------------------------Funcao---------------------------------------

fun getDiasAlugados[v: Veiculo] : set Dia {
	v.diaAlugado
}

fun getCliente[v: Veiculo] : lone Cliente {
	v.cliente
}

pred show [ ] { }

run show for 4
