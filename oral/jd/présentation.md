# Présentation

## Introduction

(Présentation de la problématique)
* En programmation, on a souvent besoin d’itérer sur des données, des valeurs…
* 2 façons d’itérer&nbsp;: boucles et fonctions récursives
* La première méthode est souvent la + répandue et est en général meilleure
  en terme de gestion de la mémoire
* La deuxième méthode est parfois préférable en terme de lisibilité du code mais
  peut entraîner des dépassement de pile (donner un exemple ?)
* Un compilateur va vouloir transformer les fonctions récursives en boucles

Schéma + annonce de plan

* On doit partir d’un texte (la fonction source) et le transformer en un autre
  texte (la boucle)
* Traiter directement un texte est assez compliqué&nbsp;: on aimerait bien
  représenter le code autrement, par exemple via un arbre sur lequel il est
  très facile d’effectuer des traitements et des modifications
* Pour construire cet arbre, on va procéder en deux étapes&nbsp;: l’analyse
  lexicale et l’analyse syntaxique

## Arbre de syntaxe abstrait

### Analyse lexicale (Mylo)

* On veut d’abord découper le texte en lexèmes&nbsp;: de petites unités de sens
  ayant la forme d’un couple (type, valeur)
* Automate&nbsp;: états et transitions
* On prend une famille d’automates qui reconnaissent chacun un type de lexème,
  et on les fait tous lire tant qu’il y en a au moins 2 qui ne sont pas bloqués.
* Quand il ne reste plus qu’un automate et qu’il a réussi à reconnaître un
  lexème, on ajoute ce lexème reconnu à la liste de lexèmes qu’on est en train
  de construire
* S’ils sont tous bloqués, on renvoie une erreur.

### Analyse syntaxique

* Automate aussi mais exécution différente
* Notion de grammaire&nbsp;: représentation d’un langage sous forme de règles
  de dérivation
* On peut construire un automate à partir d’une grammaire
* L’exécution de l’automate est différente que pour l’analyse lexicale&nbsp;:
  pile d’arbres et pile d’états + donner un exemple
* Parler du fait que LR(0) ne fonctionnera pas pour OCaml et qu’on utilisera
  LR(1) qui est très similaire (mettre LR(1) en annexe)


### Conclusion

Super, on a transformé du texte en arbres qu’on va pouvoir maintenant
modifier.

## Transformation en boucles

On veut donc transformer les fonctions récursives en boucles. On va d’abord les
transformer en fonctions récursives terminales.

### Mise sous forme de boucle

* On place chaque argument dans un `ref`
* À chaque appel récursif, on change la valeur des `ref` puis on refait un tour
  de boucle
* Lorsqu’une valeur est renvoyée, on met la condition de la boucle à `false`

* Montrer les problèmes que ça pose
* Solution&nbsp;: récursivité terminale

## Conclusion&nbsp;: résultats

(Montrer que notre code fonctionne mieux dans certains cas, là où une méthode
récursive naïve plante (dépassement de pile))

## Annexes

### LR(1)

* Exemple de pourquoi OCaml n’est pas LR(0) (nécessité de LR(1))&nbsp;
* Détail de l’algo

### Détailler sur les grammaires&nbsp;?

À voir
