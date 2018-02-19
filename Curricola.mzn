
int: m;
int: k;
array[1..m] of int: ac; 
array[1..m] of int: hc; 
array[1..m] of string: corsi;
array[1..k] of string: docenti;
array[1..k, 1..m] of int: insegna; 

array[1..m] of var 1..k: orario;									%array da riempire

predicate puoinsegnare(var int:docente, int:corso) =
	insegna[docente,corso] = 1;
	
constraint forall (i in 1..m, j in 1..m where i!=j) (				%un docente non può insegnare più di un corso nello stesso anno curricolare;
	if ac[i] == ac[j] then
		orario[i] != orario[j]
	else
		true
	endif
);
	
constraint forall (i in 1..m ) ( 
	puoinsegnare( orario[i], i )									%i docenti possono insegnare solo corsi di cui sono competenti;
);

constraint forall(j in 1..m , g in 1..m)(							
	sum([hc[i]*bool2int(orario[i] == orario[j]) | i in 1..m]) - 	% Controllo che il carico complessivo di ciascun docente
	sum([hc[i]*bool2int(orario[i] == orario[g]) | i in 1..m]) <= 2	% non sia superiore di due ore a quello di un altro docente;
);

solve:: int_search ([orario[a] | a in 1..k], first_fail, indomain_min, complete) satisfy;

output 	["\nPRIMO ANNO\n"] ++ 
			[ if ac[a] == 1 then show(corsi[a]) ++ ": " ++ show(docenti[fix(orario[a])]) ++ "\n" else "" endif| a in 1..m] ++
		["\nSECONDO ANNO\n"] ++ 
			[ if ac[a] == 2 then show(corsi[a]) ++ ": " ++ show(docenti[fix(orario[a])]) ++ "\n" else "" endif| a in 1..m] ++
		["\nTERZO ANNO\n"] ++ 
			[ if ac[a] == 3 then show(corsi[a]) ++ ": " ++ show(docenti[fix(orario[a])]) ++ "\n" else "" endif| a in 1..m];