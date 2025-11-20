# Tunnel Network Routing - SAT Reduction

## 📋 Description

Ce projet implémente une réduction SAT pour résoudre le problème de routage dans les réseaux de tunnels IPv4/IPv6. Le problème consiste à trouver un chemin simple entre un nœud source et un nœud destination dans un réseau où chaque nœud peut effectuer des opérations sur une pile de protocoles (IPv4 ou IPv6).

## 🎯 Objectif

Étant donné un réseau de tunnels avec :
- Des nœuds pouvant effectuer des opérations : **PUSH**, **POP**, **TRANSMIT**
- Une pile de protocoles (4 = IPv4, 6 = IPv6)
- Un nœud source et un nœud destination

Trouver un **chemin simple** (sans cycles) qui permet d'aller de la source à la destination en respectant les contraintes de la pile.

## 🔧 Approche : Réduction SAT

Le problème est réduit à un problème de satisfiabilité (SAT) en utilisant le solveur Z3. Le chemin est encodé par des variables booléennes représentant :

### Variables principales

1. **`x_{node,pos,height}`** : Variable booléenne vraie ssi on est au nœud `node` à la position `pos` du chemin avec une pile de hauteur `height`

2. **`y_{pos,height,4}`** : Variable booléenne vraie ssi la cellule de hauteur `height` contient le protocole 4 (IPv4) à la position `pos`

3. **`y_{pos,height,6}`** : Variable booléenne vraie ssi la cellule de hauteur `height` contient le protocole 6 (IPv6) à la position `pos`

### Contraintes implémentées

#### φ₁ : Unicité de l'état
À chaque position du chemin, on se trouve dans **exactement un** état (couple nœud-hauteur).

#### φ₂ : Conditions de départ et d'arrivée
- Le chemin commence au nœud source avec une pile contenant uniquement `[4]`
- Le chemin se termine au nœud destination avec une pile contenant uniquement `[4]`

#### φ₃ : Transitions valides
Pour chaque état `(u, i, h)`, les contraintes garantissent que :
- On ne peut aller que vers des **nœuds voisins** (arêtes existantes)
- Le **changement de hauteur** est valide : -1 (POP), 0 (TRANSMIT), ou +1 (PUSH)
- L'**action du nœud** correspond à l'opération effectuée :
  - **TRANSMIT_4** : la pile reste identique, le sommet contient 4
  - **TRANSMIT_6** : la pile reste identique, le sommet contient 6
  - **PUSH_X_Y** : ajoute Y au sommet, l'ancien sommet contient X
  - **POP_X_Y** : retire le sommet Y, le nouveau sommet contient X

#### φ₄ : Pile bien définie
Chaque cellule utilisée de la pile contient **exactement un protocole** (soit 4, soit 6, jamais les deux, jamais aucun).

#### φ₅ : Cohérence action-pile (intégré dans φ₃)
Le contenu du sommet de la pile est cohérent avec l'opération effectuée par le nœud.

#### φ₆ : Évolution de la pile
La pile évolue correctement lors des transitions :
- **TRANSMIT** : toute la pile reste identique
- **PUSH** : un nouvel élément est ajouté, le reste est préservé
- **POP** : le sommet est retiré, le reste est préservé

#### φ₈ : Chemin simple
On ne peut pas visiter le même état `(nœud, hauteur)` deux fois.

## 🏗️ Structure du code

### Fichier principal : `TunnelReduction.c`

**Fonctions clés :**

- `tn_path_variable()` : Crée la variable `x_{node,pos,height}`
- `tn_4_variable()` : Crée la variable `y_{pos,height,4}`
- `tn_6_variable()` : Crée la variable `y_{pos,height,6}`
- `get_stack_size()` : Calcule la taille maximale de la pile

**Fonctions de contraintes :**

- `unicité()` : Génère φ₁
- `contrainte_depart_arrivee()` : Génère φ₂
- `creer_contraintes_transitions()` : Génère φ₃ (+ φ₅ intégré)
- `creer_contrainte_pile_bien_definie()` : Génère φ₄
- `create_stack_evolution_constraint()` : Génère φ₆
- `create_simple_path_constraint()` : Génère φ₈

**Fonction principale :**

- `tn_reduction()` : Combine toutes les contraintes et retourne la formule SAT complète

**Fonctions utilitaires :**

- `tn_get_path_from_model()` : Extrait le chemin solution du modèle Z3
- `tn_print_model()` : Affiche le modèle pour le débogage

## 🚀 Utilisation

### Compilation
```bash
make
```

### Exécution
```bash
./graphProblemSolver -R -c  -t 
```

**Options :**
- `-R` : Mode réduction SAT
- `-c <n>` : Longueur maximale du chemin à explorer
- `-t <fichier>` : Fichier .dot du réseau de tunnels

### Exemples
```bash
# Exemple 1 : réseau simple
./graphProblemSolver -R -c 5 -t graphs/TunnelNetwork/exemple1.dot

# Exemple 2 : réseau moyen
./graphProblemSolver -R -c 10 -t graphs/TunnelNetwork/exemple2.dot

# Exemple 3 : réseau complexe
./graphProblemSolver -R -c 20 -t graphs/TunnelNetwork/exemple3.dot
```

## 📊 Résultats

Le solveur explore itérativement les longueurs de chemin de 1 à `n` jusqu'à trouver une solution.

**Sortie exemple :**
```
--- size 17 ---
formula for size 17 computed in 0.59 seconds
solution computed in 2.41 seconds
There is a simple path of size 17.
s -(4→4)-> u1 -(4↑46)-> u2 -(6↑64)-> u3 ... -(46↓4)-> end
```

**Notation des opérations :**
- `4→4` : TRANSMIT IPv4
- `6→6` : TRANSMIT IPv6
- `4↑46` : PUSH IPv4, ajoute IPv6
- `46↓4` : POP, retire IPv6, révèle IPv4

## ⚙️ Optimisations implémentées

1. **Allocation dynamique** : Utilisation de `malloc()` pour éviter les stack overflow sur les grandes instances
2. **Contraintes strictes** : Interdiction explicite des transitions invalides (changements de hauteur > 1, arêtes inexistantes)
3. **Intégration de contraintes** : φ₅ intégré dans φ₃ pour réduire la redondance

## 🔍 Points techniques importants

### Gestion de la pile

La taille maximale de la pile est calculée par : `taille_max = length / 2 + 1`

Cela permet d'optimiser l'espace de recherche tout en garantissant qu'on a suffisamment de place pour toutes les opérations PUSH nécessaires.

### Non-déterminisme du solveur

Le solveur Z3 peut trouver **plusieurs solutions valides différentes** pour un même problème. Deux exécutions (ou deux implémentations correctes) peuvent donc produire des chemins différents de même longueur.

### Complexité

La complexité de la formule SAT générée est :
- **Variables** : O(n × nodes × stack_size)
- **Contraintes** : O(n × nodes² × stack_size²)

où `n` est la longueur du chemin.

## 📚 Dépendances

- **Z3 Solver** : Bibliothèque SMT solver pour résoudre les formules SAT
- **GCC** : Compilateur C avec support C99+
- **Make** : Système de build

## 🐛 Débogage

Pour activer les messages de débogage, décommentez les sections `DEBUG` dans :
- `tn_get_path_from_model()` : Pour voir l'extraction du chemin
- `tn_reduction()` : Pour voir les informations sur le graphe et les arêtes

## 📝 Notes

- Le projet respecte les spécifications du problème de routage dans les réseaux de tunnels
- Les solutions trouvées sont **optimales** en longueur
- Le code est conforme aux standards de programmation C (ANSI C99)
- Tous les tests passent avec succès

## 👤 Auteur

Oubakki AYoub et Mahmoud Mounouar 

## 📄 Licence

Ce projet a été réalisé dans le cadre du cours de Complexité et Calculabilité.