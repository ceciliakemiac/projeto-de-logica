module locadora

one sig Inventario {
	veiculos: set Veiculo
}

abstract sig Veiculo {}
sig VeiculoInativo extends Veiculo {}
sig VeiculoAtivo extends Veiculo {}


-- Todos os veiculos estao cadastrados no inventario
fact Veiculo{
	all v: Veiculo | one veiculos.v
}

pred show[]{}
run show for 5
