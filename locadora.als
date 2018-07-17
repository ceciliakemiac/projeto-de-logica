module Locadora

one sig Locadora {
	inativos: set Veiculo,
	ativos: set Veiculo
}

abstract sig Veiculo {
	anos: some Ano
}

sig Helicoptero extends Veiculo { }
sig Motocicleta extends Veiculo { }
sig Carro extends Veiculo { }

sig Ano {
	veiculo: one Veiculo
}

---------------------------------Fatos-------------------------------

fact VeiculosCadastrados {
	all v: Veiculo | one inativos.v => no ativos.v
	all v: Veiculo | one ativos.v => no inativos.v
}

fact {
	all v: Veiculo | one inativos.v or one ativos.v
}

fact AnosParaCadaVeiculo {
	anos = ~veiculo
}

fact AnosDeUso {
	all v: Veiculo | one inativos.v => #v.anos > 5
	all v: Veiculo | one ativos.v => #v.anos <= 5
}

pred show [ ] { }

run show for 10
