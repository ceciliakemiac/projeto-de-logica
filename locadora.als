module Locadora

one sig Locadora {
	helicoptero: set Veiculo,
	motocicleta: set Veiculo,
	carro: set Veiculo
}

abstract sig Veiculo {
	anos: some Ano
}

sig Inativo extends Veiculo { }
sig Ativo extends Veiculo { }

sig Ano {
	veiculo: one Veiculo
}

---------------------------------Fatos-------------------------------

fact VeiculosCadastrados {
	all v: Veiculo | one helicoptero.v => no motocicleta.v and no carro.v
	all v: Veiculo | one motocicleta.v => no helicoptero.v and no carro.v
	all v: Veiculo | one carro.v => no helicoptero.v and no motocicleta.v

	all v: Veiculo | one helicoptero.v or one motocicleta.v or one carro.v
}

fact AnosParaCadaVeiculo {
	anos = ~veiculo
}

fact {
	all i: Inativo | anosInativos[ i ]
}

fact {
	all a: Ativo | anosAtivos[ a ]
}

pred anosInativos[i: Inativo] {
	#i.anos > 5
}

pred anosAtivos[a: Ativo] {
	#a.anos <= 5
}
<<<<<<< HEAD
=======
//fact AnosDeUso {
	//all v: Veiculo | one inativos.v => #v.anos > 5
	//all v: Veiculo | one ativos.v => #v.anos <= 5
//}
>>>>>>> 14512c21aa09bd8b09ecd03998e84b60e038c672

pred show [ ] { }

run show for 10

