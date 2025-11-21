#include "TunnelReduction.h"
#include "Z3Tools.h"
#include <stdio.h>
#include <stdlib.h>  

/**
 * @brief Creates the variable "x_{node,pos,stack_height}" of the reduction (described in the subject).
 *
 * @param ctx The solver context.
 * @param node A node.
 * @param pos The path position.
 * @param stack_height The highest cell occupied of the stack at that position.
 * @return Z3_ast
 */
Z3_ast tn_path_variable(Z3_context ctx, int node, int pos, int stack_height)
{
    char name[60];
    snprintf(name, 60, "node %d,pos %d, height %d", node, pos, stack_height);
    return mk_bool_var(ctx, name);
}

/**
 * @brief Creates the variable "y_{pos,height,4}" of the reduction (described in the subject).
 *
 * @param ctx The solver context.
 * @param pos The path position.
 * @param height The height of the cell described.
 * @return Z3_ast
 */
Z3_ast tn_4_variable(Z3_context ctx, int pos, int height)
{
    char name[60];
    snprintf(name, 60, "4 at height %d on pos %d", height, pos);
    return mk_bool_var(ctx, name);
}

/**
 * @brief Creates the variable "y_{pos,height,6}" of the reduction (described in the subject).
 *
 * @param ctx The solver context.
 * @param pos The path position.
 * @param height The height of the cell described.
 * @return Z3_ast
 */
Z3_ast tn_6_variable(Z3_context ctx, int pos, int height)
{
    char name[60];
    snprintf(name, 60, "6 at height %d on pos %d", height, pos);
    return mk_bool_var(ctx, name);
}

/**
 * @brief Wrapper to have the correct size of the array representing the stack (correct cells of the stack will be from 0 to (get_stack_size(length)-1)).
 *
 * @param length The length of the sought path.
 * @return int
 */
int get_stack_size(int length)
{
    return length / 2 + 1;
}

/**
 * @brief Crée la contrainte φ₁ : Unicité de l'état à chaque position
 * Cette fonction garantit qu'à chaque position du chemin, on se trouve
 * dans exactement un état (un couple nœud-hauteur).
 * 
 * @param ctx Le contexte Z3 (notre "atelier de travail")
 * @param resau Le réseau de tunnels (notre graphe)
 * @param length La longueur du chemin recherché
 * @return Z3_ast La formule de contrainte complète
 */
Z3_ast unicité(Z3_context ctx, TunnelNetwork reseau, int length){
    int nombre_noeuds = tn_get_num_nodes(reseau);
    int taille_max_pile = get_stack_size(length);
    
   //Créer un tableau pour stocker les contraintes
    Z3_ast position_constraints[length + 1];
     // Pour chaque position i, créer la contrainte d'unicité
    for (int i = 0; i <= length; i++){
        int nombre_etat_possibles = nombre_noeuds * taille_max_pile;
        //Créer un tableau contient toutes les variables x_{nœud,position,hauteur} pour position i
        Z3_ast x[nombre_etat_possibles];
        int cnt = 0;
        
        for (int node = 0; node < nombre_noeuds; node++){
            for (int h = 0; h < taille_max_pile; h++){
                // tn_path_variable creér notre variable booléan x(node,i,h)
                x[cnt++] = tn_path_variable(ctx, node, i, h);
            }
        }
        //Parmi ces variables, EXACTEMENT UNE doit être vraie** (var1 ou var2 ou .... ou varN) pour une position i
        position_constraints[i] = uniqueFormula(ctx, x, nombre_etat_possibles);
    }
    return Z3_mk_and(ctx, length + 1, position_constraints);
}

/**
 * @brief Crée la contrainte φ₂ : Conditions de départ et d'arrivée
 * 
 * Cette fonction génère une formule logique qui assure que :
 * - Le chemin commence au nœud source avec une pile vide (hauteur 0)
 * - Le chemin se termine au nœud destination avec une pile vide (hauteur 0)
 * - La pile contient le marqueur spécial '4' au fond (hauteur 0) au début et à la fin
 * 
 * @param ctx Contexte Z3 pour créer les formules logiques
 * @param reseau Le réseau de tunnels contenant les nœuds source et destination
 * @param longueur Longueur du chemin à explorer
 * @return Z3_ast La formule de contrainte combinée (conjonction des 4 conditions)
 */
Z3_ast contrainte_depart_arrivee(Z3_context ctx, TunnelNetwork reseau, int length){
    int depart = tn_get_initial(reseau);
    int arriv = tn_get_final(reseau);
    Z3_ast constraints[4];
    
    // au nœud depart, hauteur 0
    constraints[0] = tn_path_variable(ctx, depart, 0, 0);
    
    // pile contient 4 à hauteur 0
    constraints[1] = tn_4_variable(ctx, 0, 0);
    
    //  au nœud destination, hauteur 0
    constraints[2] = tn_path_variable(ctx, arriv, length, 0);
    
    // pile contient 4 à hauteur 0
    constraints[3] = tn_4_variable(ctx, length, 0);
    return Z3_mk_and(ctx, 4, constraints);
}

/**
 * @brief Crée les contraintes φ₃ + φ₇ : Cohérence hauteur-opération et transitions du graphe
 * 
 * Cette fonction génère les règles de transition qui définissent comment on peut se déplacer
 * dans le réseau de tunnels en respectant les opérations sur la pile (PUSH, POP, TRANSMIT).
 * 
 * Pour chaque état possible (nœud, position, hauteur), elle crée une règle :
 * "SI je suis dans cet état ALORS je dois aller vers l'un des états successeurs autorisés"
 * 
 * @param ctx Contexte Z3 pour créer les formules logiques
 * @param reseau Le réseau de tunnels avec ses nœuds et arêtes
 * @param length Longueur du chemin à explorer
 * @return Z3_ast La formule de contrainte combinée (conjonction de toutes les règles)
 */

Z3_ast creer_contraintes_transitions(Z3_context ctx, TunnelNetwork reseau, int length)
{
    int nombre_noeuds = tn_get_num_nodes(reseau);
    int taille_max_pile = get_stack_size(length);

    // Allouer dynamiquement sur le tas au lieu de la pile
    int max_constraints = length * nombre_noeuds * nombre_noeuds * taille_max_pile * 30;
    Z3_ast *toutes_contraintes = (Z3_ast *)malloc(max_constraints * sizeof(Z3_ast));
    if (toutes_contraintes == NULL) {
        fprintf(stderr, "Erreur: impossible d'allouer la mémoire pour les contraintes\n");
        exit(1);
    }

    int nb_contraintes = 0;
    // CONTRAINTE 1 : Interdire les transitions avec changement de hauteur invalide
    // Seuls les changements de hauteur -1, 0, +1 sont autorisés
    for (int i = 0; i < length; i++){
        for (int noeud = 0; noeud < nombre_noeuds; noeud++){
            for (int h = 0; h < taille_max_pile; h++){
                Z3_ast x_noeud = tn_path_variable(ctx, noeud, i, h);
                
                for (int noeud_suiv = 0; noeud_suiv < nombre_noeuds; noeud_suiv++){
                    for (int h_prime = 0; h_prime < taille_max_pile; h_prime++){
                        int delta = h_prime - h;
                        // Si le changement de hauteur est invalide (pas -1, 0, ou +1)
                        if (delta < -1 || delta > 1){
                            Z3_ast x_noeud_suiv = tn_path_variable(ctx, noeud_suiv, i + 1, h_prime);
                            Z3_ast forbidden = Z3_mk_and(ctx, 2, (Z3_ast[]){x_noeud, x_noeud_suiv});
                            toutes_contraintes[nb_contraintes++] = Z3_mk_not(ctx, forbidden);
                        }
                    }
                }
            }
        }
    }
    // CONTRAINTE 2 : Interdire les transitions vers des nœuds non-voisins
    // CONTRAINTE 3 : Vérifier la cohérence pile-action pour les transitions valides

    for (int i = 0; i < length; i++){
        for (int noeud = 0; noeud < nombre_noeuds; noeud++){
            for (int haut = 0; haut < taille_max_pile; haut++){
                Z3_ast x_noeud = tn_path_variable(ctx, noeud, i, haut);
                for (int noeud_suiv = 0; noeud_suiv < nombre_noeuds; noeud_suiv++){
                    // Si l'arête noeud->noeud_suiv N'EXISTE PAS
                    if (!tn_is_edge(reseau, noeud, noeud_suiv)){
                        // Interdire TOUTES les transitions vers noeud_suiv depuis noeud

                        // TRANSMIT
                        Z3_ast etat_suivant_meme_hauteur = tn_path_variable(ctx, noeud_suiv, i + 1, haut);
                        Z3_ast contrainte_interdite_transmission = Z3_mk_and(ctx, 2, (Z3_ast[]){x_noeud, etat_suivant_meme_hauteur});
                        toutes_contraintes[nb_contraintes++] = Z3_mk_not(ctx, contrainte_interdite_transmission);
                        // PUSH 
                        if (haut + 1 < taille_max_pile){
                            Z3_ast etat_suivant_apres_push = tn_path_variable(ctx, noeud_suiv, i + 1, haut + 1);
                            Z3_ast contrainte_interdite_push = Z3_mk_and(ctx, 2, (Z3_ast[]){x_noeud, etat_suivant_apres_push});
                            toutes_contraintes[nb_contraintes++] = Z3_mk_not(ctx, contrainte_interdite_push);
                        }
                        // POP 
                        if (haut > 0){
                            Z3_ast etat_suivant_apres_pop = tn_path_variable(ctx, noeud_suiv, i + 1, haut - 1);
                            Z3_ast contrainte_interdite_pop = Z3_mk_and(ctx, 2, (Z3_ast[]){x_noeud, etat_suivant_apres_pop});
                            toutes_contraintes[nb_contraintes++] = Z3_mk_not(ctx, contrainte_interdite_pop);
                        }
                        continue;
                    }
                    // L'arête noeud->noeud_suiv EXISTE, vérifier la cohérence des actions

                    // ---- TRANSMIT ----
                    Z3_ast etat_suivant_meme_hauteur = tn_path_variable(ctx, noeud_suiv, i + 1, haut);
                    Z3_ast contrainte_transmission = Z3_mk_and(ctx, 2, (Z3_ast[]){x_noeud, etat_suivant_meme_hauteur});
                    Z3_ast conditions_transmit[10];
                    int nb_conditions_transmit = 0;
                    if (tn_node_has_action(reseau, noeud, transmit_4)){
                        conditions_transmit[nb_conditions_transmit++] = tn_4_variable(ctx, i, haut);
                    }
                    if (tn_node_has_action(reseau, noeud, transmit_6)){
                        conditions_transmit[nb_conditions_transmit++] = tn_6_variable(ctx, i, haut);
                    }
                    if (nb_conditions_transmit > 0){
                        Z3_ast transmission_valide = Z3_mk_or(ctx, nb_conditions_transmit, conditions_transmit);
                        toutes_contraintes[nb_contraintes++] = Z3_mk_implies(ctx, contrainte_transmission, transmission_valide);
                    }
                    else{
                        // Si aucune action TRANSMIT n'est disponible, interdire cette transition
                        toutes_contraintes[nb_contraintes++] = Z3_mk_not(ctx, contrainte_transmission);
                    }
                    // ---- PUSH ----
                    if (haut + 1 < taille_max_pile){
                        Z3_ast etat_suivant_apres_push = tn_path_variable(ctx, noeud_suiv, i + 1, haut + 1);
                        Z3_ast transition_push  = Z3_mk_and(ctx, 2, (Z3_ast[]){x_noeud, etat_suivant_apres_push});
                        Z3_ast conditions_push[10];
                        int nb_conditions_push = 0;
                        
                        if (tn_node_has_action(reseau, noeud, push_4_4)){
                            Z3_ast cond = Z3_mk_and(ctx, 2, (Z3_ast[]){
                                tn_4_variable(ctx, i, haut),
                                tn_4_variable(ctx, i + 1, haut + 1)
                            });
                            conditions_push[nb_conditions_push++] = cond;
                        }
                        if (tn_node_has_action(reseau, noeud, push_4_6)){
                            Z3_ast cond = Z3_mk_and(ctx, 2, (Z3_ast[]){
                                tn_4_variable(ctx, i, haut),
                                tn_6_variable(ctx, i + 1, haut + 1)
                            });
                            conditions_push[nb_conditions_push++] = cond;
                        }
                        if (tn_node_has_action(reseau, noeud, push_6_4)){
                            Z3_ast cond = Z3_mk_and(ctx, 2, (Z3_ast[]){
                                tn_6_variable(ctx, i, haut),
                                tn_4_variable(ctx, i + 1, haut + 1)
                            });
                            conditions_push[nb_conditions_push++] = cond;
                        }
                        if (tn_node_has_action(reseau, noeud, push_6_6)){
                            Z3_ast cond = Z3_mk_and(ctx, 2, (Z3_ast[]){
                                tn_6_variable(ctx, i, haut),
                                tn_6_variable(ctx, i + 1, haut + 1)
                            });
                            conditions_push[nb_conditions_push++] = cond;
                        }
                        if (nb_conditions_push > 0){
                            Z3_ast push_valide  = Z3_mk_or(ctx, nb_conditions_push, conditions_push);
                            toutes_contraintes[nb_contraintes++] = Z3_mk_implies(ctx, transition_push , push_valide );
                        }
                        else{
                            toutes_contraintes[nb_contraintes++] = Z3_mk_not(ctx, transition_push );
                        }
                    }
                    // ---- POP ----
                    if (haut > 0){
                        Z3_ast etat_suivant_apres_pop = tn_path_variable(ctx, noeud_suiv, i + 1, haut - 1);
                        Z3_ast transition_pop = Z3_mk_and(ctx, 2, (Z3_ast[]){x_noeud, etat_suivant_apres_pop});
                        Z3_ast conditions_pop[10];
                        int nb_conditions_pop = 0;
                        if (tn_node_has_action(reseau, noeud, pop_4_4)){
                            Z3_ast cond = Z3_mk_and(ctx, 2, (Z3_ast[]){
                                tn_4_variable(ctx, i, haut),
                                tn_4_variable(ctx, i, haut - 1)
                            });
                            conditions_pop[nb_conditions_pop++] = cond;
                        }
                        if (tn_node_has_action(reseau, noeud, pop_4_6)) {
                            Z3_ast cond = Z3_mk_and(ctx, 2, (Z3_ast[]){
                                tn_6_variable(ctx, i, haut),
                                tn_4_variable(ctx, i, haut - 1)
                            });
                            conditions_pop[nb_conditions_pop++] = cond;
                        }
                        if (tn_node_has_action(reseau, noeud, pop_6_4)){
                            Z3_ast cond = Z3_mk_and(ctx, 2, (Z3_ast[]){
                                tn_4_variable(ctx, i, haut),
                                tn_6_variable(ctx, i, haut - 1)
                            });
                            conditions_pop[nb_conditions_pop++] = cond;
                        }
                        if (tn_node_has_action(reseau, noeud, pop_6_6)){
                            Z3_ast cond = Z3_mk_and(ctx, 2, (Z3_ast[]){
                                tn_6_variable(ctx, i, haut),
                                tn_6_variable(ctx, i, haut - 1)
                            });
                            conditions_pop[nb_conditions_pop++] = cond;
                        }
                        if (nb_conditions_pop > 0){
                            Z3_ast pop_valide  = Z3_mk_or(ctx, nb_conditions_pop, conditions_pop);
                            toutes_contraintes[nb_contraintes++] = Z3_mk_implies(ctx, transition_pop, pop_valide );
                        }
                        else{
                            toutes_contraintes[nb_contraintes++] = Z3_mk_not(ctx, transition_pop);
                        }
                    }
                }
                
                int nb_transitions_possibles = 0;
                Z3_ast transitions_possibles[nombre_noeuds * 3];
                for (int noeud_suiv = 0; noeud_suiv < nombre_noeuds; noeud_suiv++){
                    if (!tn_is_edge(reseau,noeud, noeud_suiv))
                        continue;
                    
                    // TRANSMIT
                    if (tn_node_has_action(reseau,noeud, transmit_4) || tn_node_has_action(reseau,noeud, transmit_6)){
                        transitions_possibles[nb_transitions_possibles++] = tn_path_variable(ctx, noeud_suiv, i + 1, haut);
                    }
                    // PUSH
                    if (haut + 1 < taille_max_pile && (tn_node_has_action(reseau,noeud, push_4_4) || tn_node_has_action(reseau,noeud, push_4_6) ||
                         tn_node_has_action(reseau,noeud, push_6_4) || tn_node_has_action(reseau,noeud, push_6_6))){
                        transitions_possibles[nb_transitions_possibles++] = tn_path_variable(ctx, noeud_suiv, i + 1, haut + 1);
                    }
                    // POP
                    if (haut > 0 && (tn_node_has_action(reseau,noeud, pop_4_4) || tn_node_has_action(reseau,noeud, pop_4_6) ||
                         tn_node_has_action(reseau,noeud, pop_6_4) || tn_node_has_action(reseau,noeud, pop_6_6))){
                        transitions_possibles[nb_transitions_possibles++] = tn_path_variable(ctx, noeud_suiv, i + 1, haut - 1);
                    }
                }
                if (nb_transitions_possibles > 0){
                    Z3_ast must_go_somewhere = Z3_mk_or(ctx, nb_transitions_possibles, transitions_possibles);
                    toutes_contraintes[nb_contraintes++] = Z3_mk_implies(ctx, x_noeud, must_go_somewhere);
                }
            }
        }
    }
    Z3_ast result = Z3_mk_and(ctx, nb_contraintes, toutes_contraintes);
    // Libérer la mémoire allouée
    free(toutes_contraintes);
    
    return result;
}
   
/**
 * @brief Crée la contrainte φ₄ : La pile est bien définie (chaque cellule de la pile contient soit 4, soit 6, jamais les deux)
 * Cette fonction garantit que chaque cellule utilisée de la pile contient exactement un protocole :
 * - Soit le 4
 * - Soit le 6
 * - Jamais les deux en même temps
 * - Jamais aucun des deux (cellule vide invalide)
 * @param ctx Contexte Z3 pour créer les formules logiques
 * @param reseau Le réseau de tunnels
 * @param length Longueur du chemin à explorer
 * @return Z3_ast La formule de contrainte combinée
 */
Z3_ast creer_contrainte_pile_bien_definie(Z3_context ctx, TunnelNetwork reseau, int length){
    int nombre_noeuds = tn_get_num_nodes(reseau);
    int taille_max_pile= get_stack_size(length);
    int nombre_contraintes  = 0;
    Z3_ast toutes_contraintes[(length + 1) * taille_max_pile* taille_max_pile];
    
    for (int i = 0; i <= length; i++){
        for (int h = 0; h < taille_max_pile; h++){
            // Condition: si la pile est de hauteur h
            int nb_vars_hauteur = 0;
            Z3_ast variables_hauteur[taille_max_pile * nombre_noeuds];
            
            for (int node = 0; node < nombre_noeuds; node++){
                for (int height = 0; height < taille_max_pile; height++){
                    if (height == h){
                        variables_hauteur[nb_vars_hauteur++] = tn_path_variable(ctx, node, i, h);
                    }
                }
            }
            Z3_ast pile_height_h = Z3_mk_or(ctx, nb_vars_hauteur, variables_hauteur);
            
            // Alors pour chaque cellule k <= h
            int nb_contraintes_cellules  = 0;
            Z3_ast contraintes_cellules[taille_max_pile];
            
            for (int k = 0; k <= h; k++){
                // La cellule contient soit 4 soit 6 
                Z3_ast contient_4  = tn_4_variable(ctx, i, k);
                Z3_ast contient_6 = tn_6_variable(ctx, i, k);
                
                Z3_ast only_4 = Z3_mk_and(ctx, 2, (Z3_ast[]){contient_4 , Z3_mk_not(ctx, contient_6)});
                Z3_ast only_6 = Z3_mk_and(ctx, 2, (Z3_ast[]){Z3_mk_not(ctx, contient_4 ), contient_6});
                
                contraintes_cellules[nb_contraintes_cellules ++] = Z3_mk_or(ctx, 2, (Z3_ast[]){only_4, only_6});
            }
            
            Z3_ast all_cells_ok = Z3_mk_and(ctx, nb_contraintes_cellules , contraintes_cellules);
            toutes_contraintes[nombre_contraintes ++] = Z3_mk_implies(ctx, pile_height_h, all_cells_ok);
        }
    }
    
    return Z3_mk_and(ctx, nombre_contraintes , toutes_contraintes);
}

/**
 * @brief L’objectif de cette fonction est de générer la contrainte φ₅ qui garantit que, pour chaque étape du chemin et chaque
 *  hauteur de pile, le contenu du sommet est cohérent avec l’opération (push, pop ou transmit) effectuée par le nœud visité. 
 * Elle encode donc correctement la sémantique de la pile dans le solveur Z3.
 * @param ctx Z3 context
 * @param reseau The tunnel network
 * @param length Path length
 * @return Z3_ast The constraint formula
 */
Z3_ast create_top_operation_constraint(Z3_context ctx, TunnelNetwork reseau, int length){
    int nombre_noeuds= tn_get_num_nodes(reseau);
    int taille_max_pile= get_stack_size(length);
    
    int nombre_contraintes = 0;
    Z3_ast toutes_contraintes[length * nombre_noeuds* nombre_noeuds* taille_max_pile* 15];
    
    for (int i = 0; i < length; i++){
        for (int noeud= 0; noeud< nombre_noeuds; noeud++){
            for (int noeud_suiv= 0; noeud_suiv< nombre_noeuds; noeud_suiv++){
                if (!tn_is_edge(reseau, noeud,noeud_suiv))
                    continue;
                for (int haut = 0; haut < taille_max_pile; haut++){
                    Z3_ast x_noeud = tn_path_variable(ctx, noeud, i, haut);
                    
                    // === TRANSMIT_4 ===
                    if (tn_node_has_action(reseau, noeud, transmit_4)){
                        Z3_ast x_noued_suiv = tn_path_variable(ctx,noeud_suiv, i + 1, haut);
                        Z3_ast transition = Z3_mk_and(ctx, 2, (Z3_ast[]){x_noeud, x_noued_suiv});
                        Z3_ast top_is_4 = tn_4_variable(ctx, i, haut);
                        toutes_contraintes[nombre_contraintes++] = Z3_mk_implies(ctx, transition, top_is_4);
                    }
                    // === TRANSMIT_6 ===
                    if (tn_node_has_action(reseau, noeud, transmit_6)){
                        Z3_ast x_noued_suiv = tn_path_variable(ctx,noeud_suiv, i + 1, haut);
                        Z3_ast transition = Z3_mk_and(ctx, 2, (Z3_ast[]){x_noeud, x_noued_suiv});
                        Z3_ast top_is_6 = tn_6_variable(ctx, i, haut);
                        toutes_contraintes[nombre_contraintes++] = Z3_mk_implies(ctx, transition, top_is_6);
                    }
                    
                    // === PUSH ===
                    if (haut + 1 < taille_max_pile){
                        Z3_ast x_noued_suiv_push = tn_path_variable(ctx,noeud_suiv, i + 1, haut + 1);
                        Z3_ast transition_push = Z3_mk_and(ctx, 2, (Z3_ast[]){x_noeud, x_noued_suiv_push});
                        // PUSH_4_4: sommet actuel=4, nouveau sommet=4
                        if (tn_node_has_action(reseau, noeud, push_4_4)){
                            Z3_ast conds[2] = {
                                tn_4_variable(ctx, i, haut),
                                tn_4_variable(ctx, i + 1, haut + 1)
                            };
                            toutes_contraintes[nombre_contraintes++] = Z3_mk_implies(ctx, transition_push, Z3_mk_and(ctx, 2, conds));
                        }
                        // PUSH_4_6: sommet actuel=4, nouveau sommet=6
                        if (tn_node_has_action(reseau, noeud, push_4_6)){
                            Z3_ast conds[2] = {
                                tn_4_variable(ctx, i, haut),
                                tn_6_variable(ctx, i + 1, haut + 1)
                            };
                            toutes_contraintes[nombre_contraintes++] = Z3_mk_implies(ctx, transition_push, Z3_mk_and(ctx, 2, conds));
                        }
                        // PUSH_6_4: sommet actuel=6, nouveau sommet=4
                        if (tn_node_has_action(reseau, noeud, push_6_4)){
                            Z3_ast conds[2] = {
                                tn_6_variable(ctx, i, haut),
                                tn_4_variable(ctx, i + 1, haut + 1)
                            };
                            toutes_contraintes[nombre_contraintes++] = Z3_mk_implies(ctx, transition_push, Z3_mk_and(ctx, 2, conds));
                        }
                        // PUSH_6_6: sommet actuel=6, nouveau sommet=6
                        if (tn_node_has_action(reseau, noeud, push_6_6)){
                            Z3_ast conds[2] = {
                                tn_6_variable(ctx, i, haut),
                                tn_6_variable(ctx, i + 1, haut + 1)
                            };
                            toutes_contraintes[nombre_contraintes++] = Z3_mk_implies(ctx, transition_push, Z3_mk_and(ctx, 2, conds));
                        }
                    }
                    
                    // === POP ===
                    if (haut > 0){
                        Z3_ast x_noued_suiv_pop = tn_path_variable(ctx,noeud_suiv, i + 1, haut - 1);
                        Z3_ast transition_pop = Z3_mk_and(ctx, 2, (Z3_ast[]){x_noeud, x_noued_suiv_pop});
                        // POP_4_4: sommet=4, sous-sommet=4
                        if (tn_node_has_action(reseau, noeud, pop_4_4)){
                            Z3_ast conds[2] = {
                                tn_4_variable(ctx, i, haut),
                                tn_4_variable(ctx, i, haut - 1)
                            };
                            toutes_contraintes[nombre_contraintes++] = Z3_mk_implies(ctx, transition_pop, Z3_mk_and(ctx, 2, conds));
                        }
                        // POP_4_6: sommet=6, sous-sommet=4
                        if (tn_node_has_action(reseau, noeud, pop_4_6)){
                            Z3_ast conds[2] = {
                                tn_6_variable(ctx, i, haut),
                                tn_4_variable(ctx, i, haut - 1)
                            };
                            toutes_contraintes[nombre_contraintes++] = Z3_mk_implies(ctx, transition_pop, Z3_mk_and(ctx, 2, conds));
                        }
                        // POP_6_4: sommet=4, sous-sommet=6
                        if (tn_node_has_action(reseau, noeud, pop_6_4)){
                            Z3_ast conds[2] = {
                                tn_4_variable(ctx, i, haut),
                                tn_6_variable(ctx, i, haut - 1)
                            };
                            toutes_contraintes[nombre_contraintes++] = Z3_mk_implies(ctx, transition_pop, Z3_mk_and(ctx, 2, conds));
                        }
                        // POP_6_6: sommet=6, sous-sommet=6
                        if (tn_node_has_action(reseau, noeud, pop_6_6)){
                            Z3_ast conds[2] = {
                                tn_6_variable(ctx, i, haut),
                                tn_6_variable(ctx, i, haut - 1)
                            };
                            toutes_contraintes[nombre_contraintes++] = Z3_mk_implies(ctx, transition_pop, Z3_mk_and(ctx, 2, conds));
                        }
                    }
                }
            }
        }
    }
    return Z3_mk_and(ctx, nombre_contraintes, toutes_contraintes);
}

/**
 * @brief Crée la contrainte φ₆ : évolution correcte de la pile
 *
 * Encode les règles d’évolution de la pile pour chaque nœud et chaque étape :
 * - TRANSMIT : pile inchangée
 * - PUSH : ajoute 4 ou 6 au sommet
 * - POP : retire le sommet
 *
 * Les contraintes sont combinées pour garantir que la pile évolue correctement
 * le long du chemin dans le réseau.
 *
 * @param ctx Contexte Z3
 * @param reseau Réseau de tunnels avec actions des nœuds
 * @param length Longueur du chemin
 * @return Z3_ast Formule φ₆ représentant la contrainte
 */

Z3_ast create_stack_evolution_constraint(Z3_context ctx, TunnelNetwork reseau, int length){
    int nombre_noeuds= tn_get_num_nodes(reseau);
    int taille_max_pile= get_stack_size(length);
    
    int num_constraints = 0;
    Z3_ast all_constraints[length * nombre_noeuds * nombre_noeuds * taille_max_pile * 10];
    
    for (int i = 0; i < length; i++){
        for (int noeud= 0; noeud< nombre_noeuds; noeud++){
            for (int noeud_suiv = 0; noeud_suiv < nombre_noeuds; noeud_suiv++){
                if (!tn_is_edge(reseau, noeud, noeud_suiv))
                    continue;
                
                for (int haut = 0; haut < taille_max_pile; haut++){
                    Z3_ast x_noeud = tn_path_variable(ctx, noeud, i, haut);

                    // TRANSMIT:
                    if (tn_node_has_action(reseau, noeud, transmit_4) || tn_node_has_action(reseau, noeud, transmit_6)){
                        Z3_ast x_noeud_suiv = tn_path_variable(ctx, noeud_suiv, i + 1, haut);
                        Z3_ast transition = Z3_mk_and(ctx, 2, (Z3_ast[]){x_noeud, x_noeud_suiv});
                        // Toutes les cellules restent identiques
                        int num_preserved = 0;
                        Z3_ast preserved[taille_max_pile * 2];
                        
                        for (int k = 0; k <= haut; k++){
                            preserved[num_preserved++] = Z3_mk_eq(ctx, tn_4_variable(ctx, i, k), tn_4_variable(ctx, i + 1, k));
                            preserved[num_preserved++] = Z3_mk_eq(ctx, tn_6_variable(ctx, i, k), tn_6_variable(ctx, i + 1, k));
                        }
                        Z3_ast preservation = Z3_mk_and(ctx, num_preserved, preserved);
                        all_constraints[num_constraints++] = Z3_mk_implies(ctx, transition, preservation);
                    }
                    
                    // PUSH
                    if (haut + 1 < taille_max_pile){
                        // PUSH 4->4: ajoute 4 au sommet
                        if (tn_node_has_action(reseau, noeud, push_4_4)){
                            Z3_ast x_noeud_suiv = tn_path_variable(ctx, noeud_suiv, i + 1, haut + 1);
                            Z3_ast transition = Z3_mk_and(ctx, 2, (Z3_ast[]){x_noeud, x_noeud_suiv});
                            int num_conds = 1;
                            Z3_ast conds[taille_max_pile * 2 + 1];
                            conds[0] = tn_4_variable(ctx, i + 1, haut + 1); // Nouveau sommet = 4
                            // Reste de la pile inchangé
                            for (int k = 0; k <= haut; k++){
                                conds[num_conds++] = Z3_mk_eq(ctx, tn_4_variable(ctx, i, k), tn_4_variable(ctx, i + 1, k));
                                conds[num_conds++] = Z3_mk_eq(ctx, tn_6_variable(ctx, i, k), tn_6_variable(ctx, i + 1, k));
                            }
                            all_constraints[num_constraints++] = Z3_mk_implies(ctx, transition, Z3_mk_and(ctx, num_conds, conds));
                        }
                        
                        // PUSH 4->6: ajoute 6 au sommet
                        if (tn_node_has_action(reseau, noeud, push_4_6)){
                            Z3_ast x_noeud_suiv = tn_path_variable(ctx, noeud_suiv, i + 1, haut + 1);
                            Z3_ast transition = Z3_mk_and(ctx, 2, (Z3_ast[]){x_noeud, x_noeud_suiv});
                            
                            int num_conds = 1;
                            Z3_ast conds[taille_max_pile * 2 + 1];
                            conds[0] = tn_6_variable(ctx, i + 1, haut + 1); // Nouveau sommet = 6
                            
                            for (int k = 0; k <= haut; k++)
                            {
                                conds[num_conds++] = Z3_mk_eq(ctx, tn_4_variable(ctx, i, k), tn_4_variable(ctx, i + 1, k));
                                conds[num_conds++] = Z3_mk_eq(ctx, tn_6_variable(ctx, i, k), tn_6_variable(ctx, i + 1, k));
                            }
                            
                            all_constraints[num_constraints++] = Z3_mk_implies(ctx, transition, Z3_mk_and(ctx, num_conds, conds));
                        }
                        
                        // PUSH 6->4 et PUSH 6->6 
                        if (tn_node_has_action(reseau, noeud, push_6_4)){
                            Z3_ast x_noeud_suiv = tn_path_variable(ctx, noeud_suiv, i + 1, haut + 1);
                            Z3_ast transition = Z3_mk_and(ctx, 2, (Z3_ast[]){x_noeud, x_noeud_suiv});
                            
                            int num_conds = 1;
                            Z3_ast conds[taille_max_pile * 2 + 1];
                            conds[0] = tn_4_variable(ctx, i + 1, haut + 1);
                            
                            for (int k = 0; k <= haut; k++){
                                conds[num_conds++] = Z3_mk_eq(ctx, tn_4_variable(ctx, i, k), tn_4_variable(ctx, i + 1, k));
                                conds[num_conds++] = Z3_mk_eq(ctx, tn_6_variable(ctx, i, k), tn_6_variable(ctx, i + 1, k));
                            }
                            
                            all_constraints[num_constraints++] = Z3_mk_implies(ctx, transition, Z3_mk_and(ctx, num_conds, conds));
                        }
                        
                        if (tn_node_has_action(reseau, noeud, push_6_6)){
                            Z3_ast x_noeud_suiv = tn_path_variable(ctx, noeud_suiv, i + 1, haut + 1);
                            Z3_ast transition = Z3_mk_and(ctx, 2, (Z3_ast[]){x_noeud, x_noeud_suiv});
                            
                            int num_conds = 1;
                            Z3_ast conds[taille_max_pile * 2 + 1];
                            conds[0] = tn_6_variable(ctx, i + 1, haut + 1);
                            
                            for (int k = 0; k <= haut; k++){
                                conds[num_conds++] = Z3_mk_eq(ctx, tn_4_variable(ctx, i, k), tn_4_variable(ctx, i + 1, k));
                                conds[num_conds++] = Z3_mk_eq(ctx, tn_6_variable(ctx, i, k), tn_6_variable(ctx, i + 1, k));
                            }
                            
                            all_constraints[num_constraints++] = Z3_mk_implies(ctx, transition, Z3_mk_and(ctx, num_conds, conds));
                        }
                    }
                    
                    // POP: retire le sommet
                    if (haut > 0 && (tn_node_has_action(reseau, noeud, pop_4_4) || tn_node_has_action(reseau, noeud, pop_4_6) ||
                                  tn_node_has_action(reseau, noeud, pop_6_4) || tn_node_has_action(reseau, noeud, pop_6_6))){
                        Z3_ast x_noeud_suiv = tn_path_variable(ctx, noeud_suiv, i + 1, haut - 1);
                        Z3_ast transition = Z3_mk_and(ctx, 2, (Z3_ast[]){x_noeud, x_noeud_suiv});
                        
                        // La pile en-dessous reste identique
                        int num_preserved = 0;
                        Z3_ast preserved[taille_max_pile * 2];
                        
                        for (int k = 0; k < haut; k++){
                            preserved[num_preserved++] = Z3_mk_eq(ctx, tn_4_variable(ctx, i, k), tn_4_variable(ctx, i + 1, k));
                            preserved[num_preserved++] = Z3_mk_eq(ctx, tn_6_variable(ctx, i, k), tn_6_variable(ctx, i + 1, k));
                        }
                        
                        all_constraints[num_constraints++] = Z3_mk_implies(ctx, transition, Z3_mk_and(ctx, num_preserved, preserved));
                    }
                }
            }
        }
    }
    
    return Z3_mk_and(ctx, num_constraints, all_constraints);
}
/**
 * @brief Crée la contrainte φ₈ : chemin simple (pas de nœud visité deux fois)
 *
 * Garantit qu’aucun état (nœud, hauteur) n’est visité à plus d’une position
 * le long du chemin dans le réseau.
 *
 * @param ctx Contexte Z3
 * @param reseau Réseau de tunnels
 * @param length Longueur du chemin
 * @return Z3_ast Formule φ₈ représentant la contrainte
 */

Z3_ast create_simple_path_constraint(Z3_context ctx, TunnelNetwork reseau, int length){
    int nombre_noeuds= tn_get_num_nodes(reseau);
    int taille_max_pile= get_stack_size(length);
    
    int nombre_contraintes = 0;
    Z3_ast toutes_contraintes[nombre_noeuds * length * length * taille_max_pile];
    
    // Pour chaque nœud noeud et hauteur haut 
    for (int noeud= 0; noeud< nombre_noeuds; noeud++){
        for (int h = 0; h < taille_max_pile; h++){
            // Pour chaque paire de positions i < j
            for (int i = 0; i <= length; i++){
                for (int j = i + 1; j <= length; j++){
                    // On ne peut pas être dans le MÊME ÉTAT (noeud,haut) à deux positions différentes
                    Z3_ast x_noeud_i = tn_path_variable(ctx, noeud, i, h);
                    Z3_ast x_noeud_j = tn_path_variable(ctx, noeud, j, h);
                    Z3_ast both = Z3_mk_and(ctx, 2, (Z3_ast[]){x_noeud_i, x_noeud_j});
                    
                    toutes_contraintes[nombre_contraintes++] = Z3_mk_not(ctx, both);
                }
            }
        }
    }
    
    return Z3_mk_and(ctx, nombre_contraintes, toutes_contraintes);
}

//((((((((((((((((()))))))))))))))))
Z3_ast tn_reduction(Z3_context ctx, const TunnelNetwork network, int length){
     printf("=== DEBUT tn_reduction, length=%d ===\n", length);
    printf("Noeud initial: %d (%s)\n", tn_get_initial(network), tn_get_node_name(network, tn_get_initial(network)));
    printf("Noeud final: %d (%s)\n", tn_get_final(network), tn_get_node_name(network, tn_get_final(network)));
    printf("Nombre de noeuds: %d\n", tn_get_num_nodes(network));
    
    // Afficher toutes les arêtes
    int num_nodes = tn_get_num_nodes(network);
    printf("Arêtes:\n");
    for (int noeud = 0; noeud < num_nodes; noeud++)
    {
        for (int noeud_suiv = 0; noeud_suiv < num_nodes; noeud_suiv++)
        {
            if (tn_is_edge(network, noeud, noeud_suiv))
            {
                printf("  %s -> %s\n", tn_get_node_name(network, noeud), tn_get_node_name(network, noeud_suiv));
            }
        }
    }
    fflush(stdout);
    
    printf("Création phi_1...\n");
    fflush(stdout);
    Z3_ast phi_1 = unicité(ctx, network, length);
    
    printf("Création phi_2...\n");
    fflush(stdout);
    Z3_ast phi_2 = contrainte_depart_arrivee(ctx, network, length);
    
    printf("Création phi_3...\n");
    fflush(stdout);
    Z3_ast phi_3 = creer_contraintes_transitions(ctx, network, length);
    
    printf("Création phi_4...\n");
    fflush(stdout);
    Z3_ast phi_4 = creer_contrainte_pile_bien_definie(ctx, network, length);
    
    printf("Création phi_6...\n");
    fflush(stdout);
    Z3_ast phi_6 = create_stack_evolution_constraint(ctx, network, length);
    
    printf("Création phi_8...\n");
    fflush(stdout);
    Z3_ast phi_8 = create_simple_path_constraint(ctx, network, length);
    
    printf("Assemblage...\n");
    fflush(stdout);
    Z3_ast constraints[6] = {phi_1, phi_2, phi_3, phi_4, phi_6, phi_8};
    
    printf("=== FIN tn_reduction ===\n");
    fflush(stdout);
    return Z3_mk_and(ctx, 6, constraints);
}
void tn_get_path_from_model(Z3_context ctx, Z3_model model, TunnelNetwork network, int bound, tn_step *path)
{
    int num_nodes = tn_get_num_nodes(network);
    int stack_size = get_stack_size(bound);
    
    printf("\n=== DEBUG tn_get_path_from_model ===\n");
    
    for (int pos = 0; pos < bound; pos++)
    {
        int src = -1;
        int src_height = -1;
        int tgt = -1;
        int tgt_height = -1;
        
        for (int n = 0; n < num_nodes; n++)
        {
            for (int height = 0; height < stack_size; height++)
            {
                if (value_of_var_in_model(ctx, model, tn_path_variable(ctx, n, pos, height)))
                {
                    src = n;
                    src_height = height;
                    printf("Position %d: noeud %s (id=%d) hauteur %d\n", 
                           pos, tn_get_node_name(network, n), n, height);
                }
                if (value_of_var_in_model(ctx, model, tn_path_variable(ctx, n, pos + 1, height)))
                {
                    tgt = n;
                    tgt_height = height;
                    if (pos == bound - 1) {
                        printf("Position %d: noeud %s (id=%d) hauteur %d\n", 
                               pos + 1, tn_get_node_name(network, n), n, height);
                    }
                }
            }
        }
        
        printf("Transition %d: %s(h=%d) -> %s(h=%d)\n", 
               pos, 
               tn_get_node_name(network, src), src_height,
               tn_get_node_name(network, tgt), tgt_height);
        
        int action = 0;
        if (src_height == tgt_height)
        {
            if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos, src_height)))
                action = transmit_4;
            else
                action = transmit_6;
        }
        else if (src_height == tgt_height - 1)
        {
            if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos, src_height)))
            {
                if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos + 1, tgt_height)))
                    action = push_4_4;
                else
                    action = push_4_6;
            }
            else if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos + 1, tgt_height)))
                action = push_6_4;
            else
                action = push_6_6;
        }
        else if (src_height == tgt_height + 1)
        {
            if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos, src_height)))
            {
                if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos + 1, tgt_height)))
                    action = pop_4_4;
                else
                    action = pop_6_4;
            }
            else if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos + 1, tgt_height)))
                action = pop_4_6;
            else
                action = pop_6_6;
        }
        
        printf("Action: %s\n", tn_string_of_stack_action(action));
        path[pos] = tn_step_create(action, src, tgt);
    }
    
    printf("=== FIN DEBUG ===\n\n");
}
void tn_print_model(Z3_context ctx, Z3_model model, TunnelNetwork network, int bound)
{
    int num_nodes = tn_get_num_nodes(network);
    int stack_size = get_stack_size(bound);
    for (int pos = 0; pos < bound + 1; pos++)
    {
        printf("At pos %d:\nState: ", pos);
        int num_seen = 0;
        for (int node = 0; node < num_nodes; node++)
        {
            for (int height = 0; height < stack_size; height++)
            {
                if (value_of_var_in_model(ctx, model, tn_path_variable(ctx, node, pos, height)))
                {
                    printf("(%s,%d) ", tn_get_node_name(network, node), height);
                    num_seen++;
                }
            }
        }
        if (num_seen == 0)
            printf("No node at that position !\n");
        else
            printf("\n");
        if (num_seen > 1)
            printf("Several pair node,height!\n");
        printf("Stack: ");
        bool misdefined = false;
        bool above_top = false;
        for (int height = 0; height < stack_size; height++)
        {
            if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos, height)))
            {
                if (value_of_var_in_model(ctx, model, tn_6_variable(ctx, pos, height)))
                {
                    printf("|X");
                    misdefined = true;
                }
                else
                {
                    printf("|4");
                    if (above_top)
                        misdefined = true;
                }
            }
            else if (value_of_var_in_model(ctx, model, tn_6_variable(ctx, pos, height)))
            {
                printf("|6");
                if (above_top)
                    misdefined = true;
            }
            else
            {
                printf("| ");
                above_top = true;
            }
        }
        printf("\n");
        if (misdefined)
            printf("Warning: ill-defined stack\n");
    }
    return;
}