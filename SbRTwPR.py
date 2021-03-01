# -*- coding: utf-8 -*- 
 
from __future__ import print_function
import math
import sys
import random
import itertools
import subprocess
import commands

from cycle_graph         import cycle_configuration_graph as Graph

def build_tree(comps, totaln, totalc):
        root = {}
        realOnes = []
        
        comps_sorted1 = sorted(comps, key=lambda tup: tup[0])
        comps_sorted2 = sorted(comps, key=lambda tup: tup[1], reverse=True)
        
        root = Node(comps_sorted1[0][0], comps_sorted2[0][1], [], False)
        
        for item in comps_sorted2:
            cmin, cmax, ccycles = item
            place = root
            keepGoing = True
            while keepGoing:
                keepGoing = False
                if place.min <= cmin < cmax <= place.max:
                    if len(place.children) > 0:
                        for child in place.children:
                            if child.min <= cmin < cmax <= child.max:
                                place = child
                                keepGoing = True

            curr = Node(cmin, cmax, ccycles, True)
            realOnes.append(curr)
            
            parentNow = curr.getParent()
            i = 0
            while i < len(place.children):
                child = place.children[i]
                if cmin < child.min < child.max < cmax:
                    child.setParent(curr)
                    del parentNow.children[i]
                    i = i - 1
                i = i + 1
            
            curr.setParent(place)

        hurdles = 0
        superhurdles = 0
        for real in realOnes:
            if real.children == []:
                hurdles = hurdles + 1
                parent = real.getParent()
                
                if len(parent.children) == 1:
                    superhurdles = superhurdles + 1

        firstChild = root.children[0]
        if firstChild.min == root.min and firstChild.max == root.max and len(realOnes) > 1:
            #if divides is not a hurdle
            if len(firstChild.children) > 1:
                
                for fcCycle in firstChild.cycles:
                    a1, a2 = min(fcCycle), max(fcCycle)
                    inside = False
                    outside = False
                    for child in firstChild.children:
                        if child.max < a2:
                            inside = True
                        elif a2 < child.min:
                            outside = True
                    if inside and outside:
                        firstChild.divideHurdle = True
                        break

            if not firstChild.divideHurdle:
                hurdles = hurdles + 1

                if len(firstChild.children) == 1:
                    secondChild = firstChild.children[0]
                    
                    if len(secondChild.children) > 1:
                        for fcCycle in secondChild.cycles:
                            a1, a2 = min(fcCycle), max(fcCycle)
                            inside = False
                            outside = False
                            for child in secondChild.children:
                                if child.max < a2:
                                    inside = True
                                elif a2 < child.min:
                                    outside = True
                            if inside and outside:
                                secondChild.divideHurdle = True
                                break
                                
                        if not secondChild.divideHurdle:
                            superhurdles = superhurdles + 1
        
        if (hurdles > 1 and hurdles == superhurdles and (hurdles // 2) == 1):
            return(totaln - totalc + hurdles + 1)
        else:
            return(totaln - totalc + hurdles)


## Tree for computing the reversal distance

class Node(dict):

    def __init__(self, vmin, vmax, cycles, isReal):
        self._parent = None 
        self.min = vmin
        self.max = vmax   
        self.cycles = cycles 
        self.real = isReal
        self.hurdle = False
        self.divideHurdle = False
        self.children = [] # collection of pointers to child Nodes

    def getParent(self):
        return self._parent

    def setParent(self, node):
        self._parent = node
        # add this node to parent's list of children
        node.children.append(self)  




h = [0 for i in range(16)]
for h_aux in range(8,12):
    h[h_aux] = [0,0]

def get_rightmost_element(cycle, position) :
    max_position = 0
    for i in range(len(cycle)) :
        if position[cycle[i]] > position[cycle[max_position]] :
            max_position = i
    return max_position

def order_cycle(cycle, position) :
    index = get_rightmost_element(cycle, position)
    new   = [] 
    new.append(cycle[index])

    if index % 2 == 0 :    
        iter_el  = (index-1) % len(cycle)
        while iter_el != index :
            new.append(cycle[iter_el])
            iter_el = (iter_el-1) % len(cycle)
    else :
        iter_el  = (index+1) % len(cycle)
        while iter_el != index :
            new.append(cycle[iter_el])
            iter_el = (iter_el+1) % len(cycle)
    return new
    
def canonical_representation(cycles, position) :
    canonicals = []
    for cycle in cycles :
        cycle     = order_cycle(cycle, position)
        canonical = []

        for i in range(0,len(cycle),2) :
            if position[cycle[i]] < position[cycle[i+1]] :
                black = -position[cycle[i+1]]
                canonical.append(black )
            else : 
                black = position[cycle[i]]
                canonical.append(black)
        canonicals.append(canonical)
    return canonicals


def get_position(permutation) : 
    n = len(permutation)-2
    position    = [-1 for i in range(0, n+2)]
    for i in range(0, n+2) :
        position[abs(permutation[i])] = i
    return position

def remove_breakpoints(graph, allowTransp) :
    cycles3 = []
    cycles_rev2   = []
    cycles_trans2fm = []
    cycles_trans2fl = []
    cycles_trans2ml = []
    node = graph.end_node
    graph.clean_visit()

    while node :
        if not node.visit :
            cycle_size = 1
            a = node.ap.ac 
            while node.index != a.index :
                a.visit    = True
                a.ap.visit = True
                cycle_size = cycle_size + 1
                a          = a.ap.ac

            a = node
            
            ## Um 2-ciclo divergente, que cria 2 novos ciclos unitarios com uma reversao
            if cycle_size == 2:
                b = a.ap.ac
                if a.index % 2 != b.index % 2:
                    i = int(round(float(a.index + 1) / 2))
                    j = int(round(float(b.index + 1) / 2)) 
                    rev2div = [i, j]
                    rev2div.sort()
                    rev2div[1] = rev2div[1] - 1
                    cycles_rev2.append(rev2div)
                    
            ## Talvez uma transposicao que cria 2 ou 3 ciclos unitarios
            else:
                while True :
                    b = a.ap.ac
                    dist_ab = 1

                    ## Usando circularidade dos ciclos.
                    while b.index != a.ac.ap.index :
                        c       = b.ap.ac
                        dist_bc = 1
                        while c.index != a.index :
                            dist_ca = cycle_size - dist_ab - dist_bc                            
                            convergent_triple = a.index % 2 == b.index % 2 == c.index % 2
                            #verifica se entre a tripla existe pelo menos 2 distancias unitarias
                            two_odds = True
                            #2020: two_odds is always True, and allowTransp is new
                            two_odds = ( ((dist_ab + dist_bc) == 2) or 
                                         ((dist_ab + dist_ca) == 2) or 
                                         ((dist_bc + dist_ca) == 2) )

                            if (convergent_triple) and two_odds :
                                ## Arestas positivas: vale a teoria original
                                if (((a.index % 2 == 1) and (a.index > c.index > b.index)) or
                                   ((a.index % 2 == 0) and (a.index > b.index > c.index))) :
                                     if cycle_size == 3 :
                                         i = int(round(float(a.index + 1) / 2))
                                         j = int(round(float(b.index + 1) / 2))
                                         k = int(round(float(c.index + 1) / 2))
                                         cycles3trans = [i, j, k]
                                         #Um 3-ciclo orientado convergente que cria 3 ciclos unitarios
                                         cycles3trans.sort()
                                         cycles3.append(cycles3trans)
                                     else :
                                         i = int(round(float(a.index + 1) / 2))
                                         j = int(round(float(b.index + 1) / 2))
                                         k = int(round(float(c.index + 1) / 2))
                                         cycles2trans = [i, j, k]
                                         #Um k-ciclo, k>3 que cria 2 ciclos unitarios, arestas positivas
                                         cycles2trans.sort()
                                         if dist_ab == dist_ca:
                                             auxtrans2 = a.index
                                         elif dist_ab == dist_bc:
                                             auxtrans2 = b.index
                                         else:
                                             auxtrans2 = c.index
                                         #transposicao que remove os dois primeiros breakpoints
                                         if int(round(float(auxtrans2 + 1) / 2)) == min(cycles2trans):
                                             cycles_trans2fm.append(cycles2trans)
                                         #transposicao que remove os dois ultimos breakpoints
                                         elif int(round(float(auxtrans2 + 1) / 2)) == max(cycles2trans):
                                             cycles_trans2ml.append(cycles2trans)
                                         #transposicao que remove os breakpoints das extremidades
                                         else:
                                             cycles_trans2fl.append(cycles2trans)
                            c = c.ap.ac
                            dist_bc = dist_bc + 1
                        b = b.ap.ac
                        dist_ab = dist_ab + 1
                    a = a.ap.ac
                    if a.index == node.index : 
                        break
        node = node.ap.ab

    if len(cycles3) > 0 and allowTransp:
        cycles3.sort()
        h[0] = h[0] + 1
        return cycles3[0]

    cycles_rev2.sort()
    cycles_trans2fm.sort()
    cycles_trans2fl.sort()
    cycles_trans2ml.sort()
    cycles2 = []

    if len(cycles_rev2) > 0:
        cycles2.append([cycles_rev2[0][0], 1, cycles_rev2[0]])
    if len(cycles_trans2ml) > 0 and allowTransp:
        cycles2.append([cycles_trans2ml[0][0], 2, cycles_trans2ml[0]])
    if len(cycles_trans2fl) > 0 and allowTransp:
        cycles2.append([cycles_trans2fl[0][0], 3, cycles_trans2fl[0]])
    if len(cycles_trans2fm) > 0 and allowTransp:
        cycles2.append([cycles_trans2fm[0][0], 4, cycles_trans2fm[0]])
    
    if len(cycles2) > 0:
        cycles2.sort()
        return cycles2[0][2]
    
    # Se nao encontrou uma operacao, retorna 0,0
    else:
        return [0,0]


def transposition(permutation,i,j,k):
    n = len(permutation)
    new = []
    for x in range(0,i):
        new.append(permutation[x])
    for x in range(j,k):
        new.append(permutation[x])
    for x in range(i,j):
        new.append(permutation[x])
    for x in range(k,n):
        new.append(permutation[x])
    return new

def reversal(permutation,i,j):
    n = len(permutation)
    new = []
    for x in range(0,i):
        new.append(permutation[x])
    for x in range(i,j+1):
        new.append(-permutation[j-x+i])
    for x in range(j+1,n):
        new.append(permutation[x])
    return new
                

############################################################################
############### Do not need to sort a real permutation #####################
############################################################################

## This class was developed to sort cycle-graph configurations. We
## apply several rules in order to make the configuration closer to
## the identity. If no rule is found, so the program returns with no
## error message. 

## If the input cycle configuration is a full component, then we
## guarantee that the final permutation is the identity.

class heuristic_sort_dias2015 :
    def __init__(self, cycles) :
        self.input = str(cycles).replace(" ", "")
        if type(cycles) == str :
            cycles      = eval(cycles)
        self.graph           = cycle_configuration_graph(cycles)
        self.graph1          = cycle_configuration_graph(cycles)
        self.start_odds      = self.graph.num_odd_cycles() 
        self.randomized      = False

        #self.h = [0 for i in range(19)]

    def sort(self, perm, frac) :
        sequence = []
        srevs = 0
        graph = self.graph
        isSafe = False

        while True :

            allowTransp = False
            if (float(srevs)/float(len(sequence)+1) >= frac):
                allowTransp = True

            operations = remove_breakpoints(graph, allowTransp)
            if operations[0] != 0:
                h[12] = h[12] + 1
                operations = [operations]
            else:
                isSafe, operations  =  self.search_not_simple_permutation(graph, allowTransp, isSafe)
                if operations : 
                    h[13] = h[13] + 1

            for op in operations :
                if len(op) == 2 :
                    ni, nj = graph.reversal(op[0],op[1])
                    if ni <= nj :
                        self.graph1.reversal(ni,nj)
                        sequence.append(tuple([ni,nj]))
                        perm = reversal(perm, ni, nj)
                        srevs = srevs+1
                else :              
                    ni, nj, nk = graph.transposition(op[0],op[1],op[2])
                    if ni != nj and nj != nk :
                        self.graph1.transposition(ni,nj,nk)
                        sequence.append(tuple([ni,nj,nk]))
                        perm = transposition(perm, ni, nj, nk)


            if not operations :
                break      

        #outputs the sorting sequence
        if graph.num_cycles() != len(perm)+1:
            print("%d %s %f" % (len(sequence), str(sequence).replace(" ", ""), float(srevs)/float(len(sequence))))
        else:
            print("%d %s %f ERROR %s" % (len(sequence), str(sequence).replace(" ", ""), float(srevs)/float(len(sequence)), str(perm).replace(" ", "")))

    ## triples is non-empty
    def select_best_triple(self, graph, triples) :
        triple = self.get_interleaving_nonoriented_triple(graph, triples, True)
        if triple :
            return triple
        
        triple = self.get_interleaving_nonoriented_triple(graph, triples, False)
        if triple :
            return triple

        return None

    ## Here we deal simply with valid 2_moves
    def search_not_simple_permutation(self, graph, allowTransp, isSafe) :
        operations = []

        ## Valid 2-moves Transposition
        triples, other_oriented_triples = self.find_oriented_triples_with_two_odd_distances(graph)
        ## Essas triplas estao da direita para a esquerda. As
        ## operacoes estao da esquerda para a direita.
        if  triples and allowTransp:
            operations = self.select_best_triple(graph, triples)
            h[3] = h[3] + 1
            if not operations :
                operations = triples[0]
            operations.reverse()


        ## Aqui eu vou tentar aplicar uma reversao em um ciclo par 
        ## antes de uma transposicao.
        if not (operations) :
            pairs  = self.find_good_pairs(graph) 

            if pairs and isSafe :

                curr_cycles = eval(str(graph.get_cycles()))
                graphRev = cycle_configuration_graph(curr_cycles)

                graphRev.transform_into_super_simple_permutation()
                cycles_simple = graphRev.get_cycles()
                size_simple = graphRev.n
                comps_simple = graphRev.get_comps()
                if len(comps_simple) == 0:
                    curr_dist = size_simple - len(cycles_simple)
                else:
                    curr_dist = build_tree(comps_simple, size_simple, len(cycles_simple))

                safe_pairs = []
                for pair in pairs:

                    curr_cycles = eval(str(graph.get_cycles()))
                    graphRev = cycle_configuration_graph(curr_cycles)
                    i = pair[0]
                    j = pair[1]
                    if i.index > j.index:
                        op0 = int(round(float(j.index + 1) / 2))
                        op1 = int(round(float(i.index + 1) / 2))
                    else:
                        op0 = int(round(float(i.index + 1) / 2))
                        op1 = int(round(float(j.index + 1) / 2))
                    graphRev.reversal(op0,op1-1)
                    graphRev.transform_into_super_simple_permutation()
                    cycles_simple = graphRev.get_cycles()
                    size_simple = graphRev.n
                    comps_simple = graphRev.get_comps()
                    if len(comps_simple) == 0:
                        pair_dist = size_simple - len(cycles_simple)
                    else:
                        pair_dist = build_tree(comps_simple, size_simple, len(cycles_simple))
                    if pair_dist < curr_dist:
                        safe_pairs.append(pair)
                        
                    if safe_pairs:
                        operations = self.get_interleaving_divergent_pair(graph, safe_pairs)
                        if not operations:
                            operations = safe_pairs[0]
                        operations.reverse()
                        h[4] = h[4]+1



            if pairs and not isSafe:
                operations = self.get_interleaving_divergent_pair(graph, pairs) 
                if not operations :
                    operations = pairs[0]
                operations.reverse()
                h[4] = h[4] + 1

        other_triples = None
        if not(operations) and allowTransp :
            triples, other_triples = self.find_nonoriented_good_0_triples(graph) 
            if triples :
                operations = self.select_best_triple(graph, triples)
                if not operations :
                    operations = triples[0]
                operations.reverse()
                h[5] = h[5] + 1

        if not(operations) and allowTransp :
            if other_triples :
                ## Aqui eu soh vou deixar passar se conseguir criar
                ## ciclos orientados. Caso contrario, eu prefiro usar
                ## a regra seguinte e quebrar o ciclo com uma reversao
                operations = self.select_best_triple(graph, other_triples)
                ## Aqui nao ajuda pegar alguem ao acaso, prefiro
                ## tentar a sorte com o proximo passo
                if operations :
                    operations.reverse()
                    h[6] = h[6] + 1


        if not(operations) and allowTransp:
            ## Segundo a minha logica, eu nao poderia chegar ateh
            ## aqui, mas eu coloquei esta serie assim mesmo.
            if other_triples :
                operations = other_triples[0]
                operations.reverse()
                h[6] = h[6] + 1

        if not(operations) and allowTransp: 
   
            ## Aqui eu tenho que tratar os casos de ciclos orientados
            ## que nao levam a uma 2-move. Eu vou simplesmente aplicar
            ## esses ciclos. Daria para provar que conseguimos uma
            ## aproximacao 2, que eh o do algoritmo mesmo.
            if  other_oriented_triples :
                operations = self.select_best_triple(graph, other_oriented_triples)
                if not operations :
                    operations = other_oriented_triples[0]
                operations.reverse()
                h[7] = h[7] + 1


        if not(operations) : 
            pairs  = self.find_almost_good_pairs(graph) 

            if pairs and isSafe: 

                curr_cycles = eval(str(graph.get_cycles()))
                graphRev = cycle_configuration_graph(curr_cycles)

                graphRev.transform_into_super_simple_permutation()
                cycles_simple = graphRev.get_cycles()
                size_simple = graphRev.n
                comps_simple = graphRev.get_comps()
                if len(comps_simple) == 0:
                    curr_dist = size_simple - len(cycles_simple)
                else:
                    curr_dist = build_tree(comps_simple, size_simple, len(cycles_simple))


                safe_pairs = []
                for pair in pairs:
                    curr_cycles = eval(str(graph.get_cycles()))
                    graphRev = cycle_configuration_graph(curr_cycles)
                    i = pair[0]
                    j = pair[1]
                    if i.index > j.index:
                        op0 = int(round(float(j.index + 1) / 2))
                        op1 = int(round(float(i.index + 1) / 2))
                    else:
                        op0 = int(round(float(i.index + 1) / 2))
                        op1 = int(round(float(j.index + 1) / 2))
                    graphRev.reversal(op0,op1-1)
                    graphRev.transform_into_super_simple_permutation()
                    cycles_simple = graphRev.get_cycles()
                    size_simple = graphRev.n
                    comps_simple = graphRev.get_comps()
                    if len(comps_simple) == 0:
                        pair_dist = size_simple - len(cycles_simple)
                    else:
                        pair_dist = build_tree(comps_simple, size_simple, len(cycles_simple))
                    if pair_dist < curr_dist:
                        safe_pairs.append(pair)

                    if safe_pairs:
                        operations = self.get_interleaving_divergent_pair(graph, safe_pairs)
                        if not operations:
                            operations = safe_pairs[0]
                        operations.reverse()
                        h[4] = h[4]+1

            if pairs and not isSafe:
                operations = self.get_interleaving_divergent_pair(graph, pairs)
                if not operations :
                    operations = pairs[0]
                operations.reverse()
                h[4] = h[4] + 1

        if operations:
            if len(operations) == 2 :         
                i = int(round(float(operations[0].index + 1) / 2))
                j = int(round(float(operations[1].index + 1) / 2))
                if i < j:
                    return isSafe, [(i, j-1),]
                else:
                    return isSafe, [(j, i-1),]
            elif len(operations) == 3 :
                i = int(round(float(operations[0].index + 1) / 2))
                j = int(round(float(operations[1].index + 1) / 2))
                k = int(round(float(operations[2].index + 1) / 2))
                return False, [(i,j,k),]
        else:
                
            curr_cycles = eval(str(graph.get_cycles()))
    
            graphRev = cycle_configuration_graph(curr_cycles)
            
            graphRev.transform_into_super_simple_permutation()
            
            cycles_simple = graphRev.get_cycles()
            size_simple = graphRev.n
            comps_simple = graphRev.get_comps()
    
            if len(comps_simple) == 0:
                curr_dist = size_simple - len(cycles_simple)
            else:
                curr_dist = build_tree(comps_simple, size_simple, len(cycles_simple))
            

            pairs = self.find_safe_rev(graph)
            for i in pairs:
                for j in reversed(pairs):
                    if i != j:
                        curr_cycles = eval(str(graph.get_cycles()))
                        graphRev = cycle_configuration_graph(curr_cycles)
                        if i.index > j.index:
                            op0 = int(round(float(j.index + 1) / 2))
                            op1 = int(round(float(i.index + 1) / 2))
                        else:
                            op0 = int(round(float(i.index + 1) / 2))
                            op1 = int(round(float(j.index + 1) / 2))
                        graphRev.reversal(op0,op1-1)
                        graphRev.transform_into_super_simple_permutation()
                        cycles_simple = graphRev.get_cycles()
                        size_simple = graphRev.n
                        comps_simple = graphRev.get_comps()
                        if len(comps_simple) == 0:
                            pair_dist = size_simple - len(cycles_simple)
                        else:
                            pair_dist = build_tree(comps_simple, size_simple, len(cycles_simple))
                        if pair_dist < curr_dist:
                            return True, [(op0, op1-1),]

            return False, []
        return False, []

##################################################
############### Several Steps ####################
##################################################

##################################################
######## Nao Assume Simple Permutation ###########
##################################################

    ##################################################
    ################### Busca de Candidatos
        
    ## Nao assume simple permutation
    def find_oriented_triples_with_two_odd_distances(self, graph) :
        ## Eu assumo que vou varrer um ciclo que inicia com (..., c,
        ## b, a)
        triples       = []
        other_triples = []
        node = graph.end_node
        graph.clean_visit()

        while node :
            if not node.visit :
                ## Calculando o tamanho do ciclo e configurando o visit
                cycle_size = 1
                a = node.ap.ac 
                while node.index != a.index :
                    a.visit    = True
                    a.ap.visit = True
                    cycle_size = cycle_size + 1
                    a          = a.ap.ac

                a = node
                
                while True : #a.index != node.index : 
                    b = a.ap.ac
                    dist_ab = 1

                    ## Usando circularidade dos ciclos.
                    while b.index != a.ac.ap.index : 
                        c       = b.ap.ac
                        dist_bc = 1
                        while c.index != a.index :
                            dist_ca = cycle_size - dist_ab - dist_bc                            
                            convergent_triple = a.index % 2 == b.index % 2 == c.index % 2
                            two_odds = ( (dist_ab % 2 == dist_bc % 2 == 1) or 
                                         (dist_ab % 2 == dist_ca % 2 == 1) or 
                                         (dist_bc % 2 == dist_ca % 2 == 1) )

                            if (convergent_triple) :
                                ## Arestas positivas: vale a teoria original
                                if (a.index % 2 == 1) and (a.index > c.index > b.index) :
                                     if two_odds :
                                         triples.append([a, c, b])
                                     else :
                                         other_triples.append([a, c, b])
                                ## Arestas negativas: a teoria muda
                                if (a.index % 2 == 0) and (a.index > b.index > c.index) :
                                    if two_odds :
                                        triples.append([a, b, c])
                                    else :
                                        other_triples.append([a, b, c])
                            c = c.ap.ac
                            dist_bc = dist_bc + 1
                        b = b.ap.ac
                        dist_ab = dist_ab + 1
                    a = a.ap.ac
                    if a.index == node.index : 
                        break
            node = node.ap.ab
        return triples, other_triples

    ## Nao assume simple permutation. Qualquer tripla formada por dois
    ## ciclos pares. Jamais usamos arestas divertes.
    def find_nonoriented_good_0_triples(self, graph) :
        def find_index(node) :
            return node.index

        graph.clean_visit()
        node   = graph.end_node
        ccount = 1 
        even_cycles = []

        ## Observe that I'm setting one node for each black edge. That
        ## will be important to check if the black edges are divergent
        ## or not.
        while node :
            if not node.visit :
                cycle_node  = node
                icount      = 1
                vertices    = []
                while not cycle_node.visit :
                    cycle_node.visit    = True
                    cycle_node.ap.visit = True
                    vertices.append(cycle_node)
                    cycle_node          = cycle_node.ap.ac
                    icount = icount + 1

                if (icount - 1) % 2 == 0 : ## Even cycles
                    even_cycles.append(vertices)
                ccount = ccount + 1
            node = node.ap.ab
        
        crossed_triples   = []
        uncrossed_triples = []
        for i in range(len(even_cycles)) :
            for j in range(i+1, len(even_cycles)) :
                for (c1,c2) in ((even_cycles[i], even_cycles[j]),(even_cycles[j],even_cycles[i])) :
    
                    for a in range(len(c1)) :
                        ## O 2 eh para garantir que a transposicao tenha
                        ## odd distance
                        ## 2020: changed two by 1 since we dont care about odd/even cycles now
                        for b in range(a+1, len(c1), 1) :
                            node_a = c1[a]
                            node_b = c1[b]
                            
                            if node_a.index > node_b.index :
                                node_a, node_b = node_b, node_a
    
                            if node_a.index % 2 == node_b.index % 2 : ## If
                                                                      ## converge

                                ## Deve existir alguem antes de
                                ## node_a.index ou depois de
                                ## node_b.index convergindo com node_c
                                ## que serah criado logo a seguir
                                side_c = [0,0]
                                for d in c2 :
                                    if (d.index < node_a.index or d.index > node_b.index) :
                                        side_c[d.index % 2] = side_c[d.index % 2] + 1

                                for c in range(len(c2)) :
                                    node_c = c2[c]

                                    # Condicoes para ser crossed: deve
                                    # existir alguem com a mesma
                                    # orientacao de node_c fora do
                                    # trecho entre node_a e node_b.
                                    crossed = ( (node_a.index < node_c.index < node_b.index) and
                                                (side_c[node_c.index % 2] > 0)) 
                                    
                                    triple = [node_a, node_b, node_c]
                                    triple.sort(key=find_index)
                                    triple.reverse()
    
                                    if crossed :
                                        crossed_triples.append(triple)
                                    else :
                                        uncrossed_triples.append(triple)
        
        return crossed_triples, uncrossed_triples


    ## Nao assume simple permutation. Qualquer tripla formada por dois
    ## ciclos pares. Jamais usamos arestas divertes.
    def find_good_pairs(self, graph) :
        graph.clean_visit()
        node   = graph.end_node
        ccount = 1 
        even_cycles = []

        ## Observe that I'm setting one node for each black edge. That
        ## will be important to check if the black edges are divergent
        ## or not.
        while node :
            if not node.visit :
                cycle_node  = node
                icount      = 1
                vertices    = []
                while not cycle_node.visit :
                    cycle_node.visit    = True
                    cycle_node.ap.visit = True
                    vertices.append(cycle_node)
                    cycle_node          = cycle_node.ap.ac
                    icount = icount + 1

                if (icount - 1) % 2 == 0 : ## Even cycles
                    even_cycles.append(vertices)
                ccount = ccount + 1
            node = node.ap.ab
        
        pairs = []
        
        for even_cycle in even_cycles :
            for a in range(len(even_cycle)) :
                ## Abaixo, o 2 eh porque queremos uma distancia impar
                ## entra a e b.
                for b in range(a+1, len(even_cycle), 2) :             
                    node_a = even_cycle[a]
                    node_b = even_cycle[b]

                    if node_a.index > node_b.index :
                        node_a, node_b = node_b, node_a

                    if node_a.index % 2 != node_b.index % 2 : ## If diverge
                        pairs.append([node_b, node_a])
        return pairs

    def find_almost_good_pairs(self, graph) :
        graph.clean_visit()
        node   = graph.end_node
        ccount = 1 
        odd_cycles = []

        ## Observe that I'm setting one node for each black edge. That
        ## will be important to check if the black edges are divergent
        ## or not.
        while node :
            if not node.visit :
                cycle_node  = node
                icount      = 1
                vertices    = []
                while not cycle_node.visit :
                    cycle_node.visit    = True
                    cycle_node.ap.visit = True
                    vertices.append(cycle_node)
                    cycle_node          = cycle_node.ap.ac
                    icount = icount + 1

                if (icount - 1) % 2 == 1 : ## Odd cycles
                    odd_cycles.append(vertices)
                ccount = ccount + 1
            node = node.ap.ab
        
        pairs = []
        
        for odd_cycle in odd_cycles :
            for a in range(len(odd_cycle)) :
                ## Abaixo, o 2 eh porque queremos uma distancia impar
                ## entra a e b.
                for b in range(a+1, len(odd_cycle), 1) :             
                    node_a = odd_cycle[a]
                    node_b = odd_cycle[b]

                    if node_a.index > node_b.index :
                        node_a, node_b = node_b, node_a

                    if node_a.index % 2 != node_b.index % 2 : ## If diverge
                        pairs.append([node_b, node_a])
        return pairs


    def find_safe_rev(self, graph) :
        graph.clean_visit()
        node   = graph.end_node
        ccount = 1 
        cycles = []

        while node :
            if not node.visit :
                cycle_node  = node
                icount      = 1
                vertices    = []
                while not cycle_node.visit :
                    cycle_node.visit    = True
                    cycle_node.ap.visit = True
                    vertices.append(cycle_node)
                    cycle_node          = cycle_node.ap.ac
                    icount = icount + 1
                
                if len(vertices) > 1:
                    cycles.append(vertices)
                ccount = ccount + 1
            node = node.ap.ab
        
        pairs = []
        
        for cycle in cycles :
            for a in cycle :
                pairs.append(a)
        return pairs

    ##################################################
    ################### Filtro de Candidatos


    def get_interleaving_nonoriented_triple(self, graph, triples, consider_two_odd_dist = False) :
        ## 1 - First we number the cycles in O(n)
        graph.clean_visit()
        node   = graph.end_node
        ccount = 1 
        cycle_size = {}


        ## Observe that I'm setting one node for each black edge. That
        ## will be important to check if the triple is divergent or
        ## not.
        while node :
            if not node.visit :
                cycle_node  = node
                icount      = 1
                while not cycle_node.visit :
                    cycle_node.visit     = True
                    cycle_node.ap.visit  = True
                    cycle_node.cycle     = ccount
                    cycle_node.ap.cycle  = ccount
                    cycle_node.pcycle    = icount ## Nao colocar no ap
                    cycle_node.ap.pyccle = 0
                    cycle_node           = cycle_node.ap.ac
                    icount = icount + 1

                cycle_size[ccount] = icount - 1 
                ccount = ccount + 1
            node = node.ap.ab


        for triple in triples :
            if self.is_interleaving_nonoriented_triple(graph, triple, cycle_size, consider_two_odd_dist) :
                return triple
        return None


    def aux_is_interleaving_nonoriented_triple(self, carray, csize, consider_two_odd_dist) :
        for side in (0, 1) : ## Which side of the black edge the node
                             ## was found. We want convergent triples,
                             ## so the nodes must be in the same side.
            if not consider_two_odd_dist :
                for region in [ carray[side][0:3] , carray[side][1:4]  ] :
                    if (region[0] and region[1] and region[2]) :
                        minimum = min(region[0]) ## Rightmost
                        maximum = max(region[2]) ## Leftmost
                        for middle in region[1] :
                            ## A tripla serah orientada
                            if  (side == 0) and (minimum < middle < maximum) : 
                                return True

                        middle   = max(region[1])
                        for maximum in region[2] :
                            if  (side == 1) and (minimum < maximum < middle) :
                                return True
                            
            else : #### Here we want two odd distance in the
                   #### cycle. The complexity increases, but I believe
                   #### it could be done more efficiently
                for region in [ carray[side][0:3] , carray[side][1:4]  ] :
                    if (region[0] and region[1] and region[2]) :
                        for minimum in region[0] :
                            for maximum in region[2] :
                                for middle in  region[1] :
                                    d1 = maximum - middle
                                    d2 = middle  - minimum
                                    two_odds = False
                                    if csize % 2 == 0 : 
                                        ## Cycle is even, we need
                                        ## only one odd distance
                                        if d1 % 2 == 1 or d2 % 2 == 1 :
                                            two_odds = True
                                    else : 
                                        ## Cycle is odd, we need
                                        ## two odd distances
                                        if d1 % 2 == 1 and d2 % 2 == 1:
                                            two_odds = True
                                    if two_odds :
                                        if side == 0 and (minimum < middle < maximum) : 
                                            return True
                                        if side == 1 and (minimum < maximum < middle) :
                                            return True
                                            
        return False
    def is_interleaving_nonoriented_triple(self, graph, triple, cycle_size, consider_two_odd_dist) :
        # 2 - Now we get the triple and divide all nodes in 4
        # regions. Also in O(n). Here we use the directions that we
        # used to number the cycles.
        a, b, c = triple
        halves = {}
        node   = graph.end_node
        
        region = 0
        while node :
            ## We avoid the triple while dividing in regions
            if node.index in (a.index, a.ap.index,
                              b.index, b.ap.index, 
                              c.index, c.ap.index) :
                region = region + 1
            else :
                if not node.cycle in halves :
                    halves[node.cycle] =  [  [[], [], [], []],  [[], [], [], []] ]
                if node.pcycle :
                    halves[node.cycle][0][region].append(node.pcycle)
                else :
                    halves[node.ap.cycle][1][region].append(node.ap.pcycle)
            node = node.ap.ab
        

        ## 3 - Temos todos os ciclos e a posicao de cada elemento em
        ## tabela. Agora precisamos verificar se existe alguma tripla
        ## nao orientada neste conjunto. Se existir, entao esta tripla
        ## nao orientada sera transformada em orientada apos a
        ## transposicao que veio como parametro. 
        for key in list(halves.keys()) :
            found = self.aux_is_interleaving_nonoriented_triple(halves[key], cycle_size[key], consider_two_odd_dist) 
            if found :
                return True
        return False



    def aux_is_interleaving_divergent_pair_wants_two_odds(self, carray, csize) :
        ## Parte 1: Verificar se tem alguem na regiao do meio que
        ## basta ser revertido para gerar uma tripla orientada
        if ( carray[0][0] and carray[1][1] and carray[0][2] ) :
            ## Sabemos que o do meio diverge, agora precisamos
            ## saber se geraria  orientado.
            for minimum in carray[0][0] :
                for maximum in carray[1][1] :
                    for middle in carray[0][2] :
                        if minimum < middle < maximum : 
                            ## Achei orientada, falta ver se eh two
                            ## odd
                            d1 = maximum - middle 
                            d2 = middle  - minimum
                            if csize % 2 == 0 : 
                                ## Cycle is even, we need
                                ## only one odd distance
                                if d1 % 2 == 1 or d2 % 2 == 1 :
                                    return True
                            else : 
                                ## Cycle is odd, we need
                                ## two odd distances
                                if d1 % 2 == 1 and d2 % 2 == 1:
                                    return True


        if ( carray[1][0] and carray[0][1] and carray[1][2] ):
            for minimum in carray[1][0] :
                for maximum in carray[1][2] :
                    for middle in carray[0][1] :
                        if minimum < middle < maximum : 
                            ## Achei orientada, falta ver se eh two
                            ## odd
                            d1 = maximum - middle 
                            d2 = middle  - minimum
                            if csize % 2 == 0 : 
                                ## Cycle is even, we need
                                ## only one odd distance
                                if d1 % 2 == 1 or d2 % 2 == 1 :
                                    two_odds = True
                            else : 
                                ## Cycle is odd, we need
                                ## two odd distances
                                if d1 % 2 == 1 and d2 % 2 == 1:
                                    two_odds = True


        ## Parte 2: Verificar se tem dois na regiao do meio que
        ## diverge do pessoal das pontas e se revertendo esses dois a
        ## gente cria um ciclo orientado.
        if ( (carray[0][0] or carray[0][2]) and  carray[1][1] > 2 ) :
            for a in range(len(carray[1][1])) :
                for b in range(a+1, len(carray[1][1])) :
                    if a < b :
                        for c in carray[0][0] + carray[0][2] :
                            triple = [a,b,c]
                            triple.sort()                            
                            d1 = triple[2] - triple[1]
                            d2 = triple[1] - triple[0]
                            if csize % 2 == 0 : 
                                ## Cycle is even, we need
                                ## only one odd distance
                                if d1 % 2 == 1 or d2 % 2 == 1 :
                                    return True
                            else : 
                                ## Cycle is odd, we need
                                ## two odd distances
                                if d1 % 2 == 1 and d2 % 2 == 1:
                                    return True


        if ( (carray[1][0] or carray[1][2]) and  carray[0][1] > 2 ) :
            for a in range(len(carray[0][1])) :
                for b in range(a+1, len(carray[0][1])) :
                    if a > b :
                        for c in carray[1][0] + carray[1][2] :
                            triple = [a,b,c]
                            triple.sort()                            
                            d1 = triple[2] - triple[1]
                            d2 = triple[1] - triple[0]
                            if csize % 2 == 0 : 
                                ## Cycle is even, we need
                                ## only one odd distance
                                if d1 % 2 == 1 or d2 % 2 == 1 :
                                    return True
                            else : 
                                ## Cycle is odd, we need
                                ## two odd distances
                                if d1 % 2 == 1 and d2 % 2 == 1:
                                    return True

        return False

    def aux_is_interleaving_divergent_pair(self, carray) :
        ## Parte 1: Verificar se tem alguem na regiao do meio que
        ## basta ser revertido para gerar uma tripla orientada
        if ( carray[0][0] and carray[1][1] and carray[0][2] ) :
            ## Sabemos que o do meio diverge, agora precisamos
            ## saber se geraria  orientado.
            minimum = min(carray[0][0])
            maximum = max(carray[1][1])
            for middle in carray[0][2] :
                if minimum < middle < maximum : ## Achei orientada
                    return True

        if ( carray[1][0] and carray[0][1] and carray[1][2] ):
            minimum = min(carray[1][0])
            maximum = max(carray[1][2])
            for middle in carray[0][1] :
                if minimum < middle < maximum : ## Achei orientada
                    return True

        ## Parte 2: Verificar se tem dois na regiao do meio que
        ## diverge do pessoal das pontas e se revertendo esses dois a
        ## gente cria um ciclo orientado.
        if ( (carray[0][0] or carray[0][2]) and  carray[1][1] > 2 ) :
            for a in range(len(carray[1][1])) :
                for b in range(a+1, len(carray[1][1])) :
                    if a < b :
                        return True

        if ( (carray[1][0] or carray[1][2]) and  carray[0][1] > 2 ) :
            for a in range(len(carray[0][1])) :
                for b in range(a+1, len(carray[0][1])) :
                    if a > b :
                        return True
        
        return False

        
    def is_interleaving_divergent_pair(self, graph, pair, cycle_size) :
        # 2 - Now we get the triple and divide all nodes in 4
        # regions. Also in O(n). Here we use the directions that we
        # used to number the cycles.
        a, b = pair
        halves = {}
        node   = graph.end_node
        
        region = 0
        while node :
            ## We avoid the triple while dividing in regions
            if node.index in (a.index, a.ap.index,
                              b.index, b.ap.index) :
                region = region + 1
            else :
                if not node.cycle in halves :
                    halves[node.cycle] =  [  [[], [], []],  [[], [], []] ]
                if node.pcycle :
                    halves[node.cycle][0][region].append(node.pcycle)
                else :
                    halves[node.ap.cycle][1][region].append(node.ap.pcycle)
            node = node.ap.ab

        for key in list(halves.keys()) :
            found = self.aux_is_interleaving_divergent_pair_wants_two_odds(halves[key], cycle_size[key])
            if found :
                return True
        return False

    def get_interleaving_divergent_pair(self, graph, pairs) :
        ## 1 - First we number the cycles in O(n)
        graph.clean_visit()
        node   = graph.end_node
        ccount = 1 
        cycle_size = {}

        ## Observe that I'm setting one node for each black edge. That
        ## will be important to check if the triple is divergent or
        ## not.
        while node :
            if not node.visit :
                cycle_node  = node
                icount      = 1
                while not cycle_node.visit :
                    cycle_node.visit     = True
                    cycle_node.ap.visit  = True
                    cycle_node.cycle     = ccount
                    cycle_node.ap.cycle  = ccount
                    cycle_node.pcycle    = icount ## Nao colocar no ap
                    cycle_node.ap.pyccle = 0
                    cycle_node           = cycle_node.ap.ac
                    icount = icount + 1

                cycle_size[ccount] = icount - 1 
                ccount = ccount + 1
            node = node.ap.ab

        for pair in pairs :
            if self.is_interleaving_divergent_pair(graph, pair, cycle_size) :
                return pair
        return None



    def check_crossing_nonoriented_convergent(self, graph, param_a, param_b, param_c) :
        a,b,c = param_a, param_b, param_c
        half1 = {}
        half2 = {}

        a = a.ap.ab
        while a != b :                    
            if a.kind == 5 :
                if not a.cycle in half1 :
                    half1[a.cycle]  = 1
                else :
                    half1[a.cycle] += 1
            a = a.ap.ab

        b = b.ap.ab

        while b != c :
            if b.kind == 5 :
                if not b.cycle in half2 :
                    half2[b.cycle]  = 1
                else :
                    half2[b.cycle] += 1
            b = b.ap.ab

        for key in list(half1.keys()) :
            if half1[key] == 1 and key in half2 and half2[key] == 1 :
                return True

        
    def search_oriented_2_transpositions_crossing_nonoriented_convergent(self, graph) :
        node = graph.end_node
        graph.clean_visit()

        while node :
            if node.kind == 2 and not node.visit :
                
                a = node
                c = a.ap.ac
                b = c.ap.ac

                a.visit = b.visit = c.visit = True

                if self.check_crossing_nonoriented_convergent(graph, a, b, c) :
                    return  c, b, a                
            node = node.ap.ab        

    def search_oriented_2_transpositions(self, graph) :
        triples = []
        graph.clean_visit()
        node = graph.end_node
        while node :
            if node.kind == 2 and not node.visit :
                a = node
                c = a.ap.ac
                b = c.ap.ac
                a.visit = b.visit = c.visit = True
                
                triples.append([c, b, a])
            node = node.ap.ab

        if len(triples) > 0 :
            return triples[0][0], triples[0][1], triples[0][2]
  
    def get_c_kind_3_and_4(self, graph) :
        graph.clean_visit()
        node = graph.end_node
        c_kind_3  = []
        c_kind_4  = []

        while node :
            if node.kind ==  3 and not node.visit :
                b2 = node
                b1 = b2.ap.ac                
                b2.visit = b1.visit = True
                c_kind_3.append([b1, b2])

            if node.kind ==  4 and not node.visit :
                b2 = node
                b1 = b2.ap.ac.ap ## we travese the ap to get the
                                 ## rightmost node in the black edge
                b2.visit = b1.visit = True
                c_kind_4.append([b1, b2])
            node = node.ap.ab
        return c_kind_3, c_kind_4

    def search_nonoriented_2_transpositions_crossed_convergent_crossing_nonoriented_convergent(self, graph) :
        c_kind_3, c_kind_4 = self.get_c_kind_3_and_4(graph)

        for i in range(len(c_kind_3)) :
            for j in range(i+1, len(c_kind_3)) :
                ci = c_kind_3[i]
                cj = c_kind_3[j]
                
                if (ci[0].index < cj[0].index < ci[1].index < cj[1].index)  :
                    if self.check_crossing_nonoriented_convergent(graph, ci[1], cj[0],ci[0]) :
                        return ci[0], cj[0], ci[1]
                    elif self.check_crossing_nonoriented_convergent(graph, cj[1], ci[1], cj[0]) :
                        return cj[0], ci[1], cj[1]
                    
                if (cj[0].index < ci[0].index < cj[1].index < ci[1].index)  :
                    if self.check_crossing_nonoriented_convergent(graph, cj[1], ci[0], cj[0]) :
                        return cj[0], ci[0], cj[1]
                    elif self.check_crossing_nonoriented_convergent(graph, ci[1], cj[1], ci[0]) :
                        return ci[0], cj[1], ci[1]

    ## O ciclo gerado eh orientado
    def search_nonoriented_2_transpositions_crossed_convergent(self, graph) :
        c_kind_3, c_kind_4 = self.get_c_kind_3_and_4(graph)

        for i in range(len(c_kind_3)) :
            for j in range(i+1, len(c_kind_3)) :
                ci = c_kind_3[i]
                cj = c_kind_3[j]
                
                if (ci[0].index < cj[0].index < ci[1].index < cj[1].index)  :
                    return ci[0], cj[0], ci[1]
                    
                if (cj[0].index < ci[0].index < cj[1].index < ci[1].index)  :
                    return cj[0], ci[0], cj[1]


    ## O ciclo gerado eh nao orientado, mas eu transformo um outro
    ## ciclo nao orientado em orientado
    def search_nonoriented_2_transpositions_uncrossed_convergent_crossing_nonoriented_convergent(self, graph) :
        def find_index(node) :
            return node.index

        c_kind_3, c_kind_4 = self.get_c_kind_3_and_4(graph)
        for i in range(len(c_kind_3)) :
            for j in range(i+1, len(c_kind_3)) :
                joined = c_kind_3[i] + c_kind_3[j]
                joined.sort(key=find_index)
                d,c,b,a = joined

                if self.check_crossing_nonoriented_convergent(graph, a, b, c) :
                    return c, b, a
                elif self.check_crossing_nonoriented_convergent(graph, b, c, d) :
                    return d, c, b


    ## O ciclo gerado eh nao orientado, mas eu nao sei como transformar
    ## alguma coisa em orientada, entao vou escolher um deles ao
    ## acaso.
    def search_nonoriented_2_transpositions_uncrossed_convergent_randomized(self, graph) :
        def find_index(node) :
            return node.index

        triples = []
        c_kind_3, c_kind_4 = self.get_c_kind_3_and_4(graph)

        for i in range(len(c_kind_3)) :
            for j in range(i+1, len(c_kind_3)) :
                joined = c_kind_3[i] + c_kind_3[j]
                joined.sort(key=find_index)
                d,c,b,a = joined
                
                if not self.randomized :
                    return c,b,a

                triples.append([c,b,a])
                triples.append([d,c,b])

        if len(triples) > 0 :
            rand = random.randrange(0, len(triples))
            return triples[rand][0], triples[rand][1], triples[rand][2]



    ## O ciclo gerado eh nao orientado, mas eu nao sei como transformar
    ## alguma coisa em orientada, entao vou escolher um deles ao
    ## acaso.
    def search_nonoriented_2_transpositions_divergent_crossing_nonoriented_convergent(self, graph) :
        def find_index(node) :
            return node.index

        c_kind_3, c_kind_4 = self.get_c_kind_3_and_4(graph)

        ## Two edges in c_3 and one edge in c_4
        for i in range(len(c_kind_3)) :
            for j in range(len(c_kind_4)) :
                triple = c_kind_3[i] + [c_kind_4[j][0]]
                triple.sort(key=find_index)
                c,b,a = triple
                if self.check_crossing_nonoriented_convergent(graph, a, b, c) :
                    return c, b, a

                triple = c_kind_3[i] + [c_kind_4[j][1]]
                triple.sort(key=find_index)
                c,b,a = triple
                if self.check_crossing_nonoriented_convergent(graph, a, b, c) :
                    return c, b, a



    def search_nonoriented_2_transpositions_divergent_randomized(self, graph) :
        def find_index(node) :
            return node.index

        triples = []
        c_kind_3, c_kind_4 = self.get_c_kind_3_and_4(graph)

        ## Two edges in c_3 and one edge in c_4
        for i in range(len(c_kind_3)) :
            for j in range(len(c_kind_4)) :
                triple = c_kind_3[i] + [c_kind_4[j][0]]
                triple.sort(key=find_index)
                
                if not self.randomized :
                    return triple

                triples.append(triple)

                triple = c_kind_3[i] + [c_kind_4[j][1]]
                triple.sort(key=find_index)
                triples.append(triple)

        if len(triples) > 0 :
            rand = random.randrange(0, len(triples))
            return triples[rand][0], triples[rand][1], triples[rand][2]


    def search_divergent_2_reversals_randomized(self, graph) :
        c_kind_3, pairs = self.get_c_kind_3_and_4(graph)
                    
            
        if len(pairs) > 0 :
            if not self.randomized :
                return pairs[0][0], pairs[0][1]

            rand = random.randrange(0, len(pairs))
            return pairs[rand][0], pairs[rand][1]
  

    def search_nonoriented_1_5_transpositions_oriented_convergent_crossing_nonoriented_convergent(self, graph) :
        node = graph.end_node
        graph.clean_visit()

        while node :
            if node.kind == 5 and not node.visit :
                
                a = node
                b = a.ap.ac
                c = b.ap.ac

                a.visit = b.visit = c.visit = True

                if self.check_crossing_nonoriented_convergent(graph, a, b, c) :
                    return  c, b, a                
            node = node.ap.ab        


    def search_nonoriented_1_5_transpositions_oriented_divergent_crossing_nonoriented_convergent(self, graph) :
        def find_index(node) :
            return node.index

        node = graph.end_node
        graph.clean_visit()

        while node :
            if node.kind == 6 and not node.visit :
                
                a = node
                b = a.ap.ac
                c = b.ap.ac
                
                if b.index % 2 == 0 :
                    b = b.ap
                if c.index % 2 == 0 :
                    c = c.ap
                
                joined = [a,b,c]
                joined.sort(key=find_index)
                c,b,a = joined

                a.visit = b.visit = c.visit = True

                if self.check_crossing_nonoriented_convergent(graph, a, b, c) :
                    return  c, b, a                
            node = node.ap.ab        


    def search_transpositions_oriented_divergent_randomized(self, graph) :
        def find_index(node) :
            return node.index

        node = graph.end_node
        graph.clean_visit()
        triples = []

        while node :
            if node.kind == 6 and not node.visit :
                
                a = node
                b = a.ap.ac
                c = b.ap.ac
                
                if b.index % 2 == 0 :
                    b = b.ap
                if c.index % 2 == 0 :
                    c = c.ap
                
                joined = [a,b,c]
                joined.sort(key=find_index)
                c,b,a = joined

                a.visit = b.visit = c.visit = True
                
                if not self.randomized :
                    return c,b,a
                triples.append([c,b,a])
            node = node.ap.ab        

        if len(triples) > 0 :
            rand = random.randrange(0, len(triples))
            return triples[rand][0], triples[rand][1], triples[rand][2]

    def search_transpositions_nonoriented_divergent_randomized(self, graph) :
        def find_index(node) :
            return node.index

        node = graph.end_node
        graph.clean_visit()
        triples = []

        while node :
            if node.kind == 7 and not node.visit :
                a = node
                b = a.ap.ac
                c = b.ap.ac
                
                if b.index % 2 == 0 :
                    b = b.ap
                    return b, a
                if c.index % 2 == 0 :
                    c = c.ap
                    return c, a

                triples.append([c,b,a])
            node = node.ap.ab        

        if len(triples) > 0 :
            rand = random.randrange(0, len(triples))
            return triples[rand][0], triples[rand][1], triples[rand][2]



############################################################################
############ Do not need to represent a real permutation ###################
############################################################################

## This class represents an unoriented cycle-graph. Keep in mind that
## this class is not the same as used for the sorting by transposition
## problem. Here, the white edges are not the reverse of the black
## edges as before. That is because the black edges can go from righ
## to left as well as to left to right.

## For instance, assume a permutation (5, 2, ...). The configuration
## in the graph would be.

## node(0).ap  = -5      ## node(0).ab  = Null
## node(-5).ab = 5       ## node(-5).ap = 0  
## node(5).ap  = -2      ## node(5).ab  = -5 
## node(-2).ab = 2       ## node(-2).ap = 5

class cycle_configuration_graph() :
    def __init__(self, cycles) : ## Ignore tells us which black edges
                                 ## we should ignore.


        ## The number of cycles was never calculated
        self.__num_cycles           = False
        self.__num_odd_cycles       = False

        
        self.__first_indice_shift   = 0 # Tell us the index of the
                                        # edge that is pointed by
                                        # begin_node. If it is
                                        # negative, than we know that
                                        # a mirror have occurred.

        # self.__mirror               = False


        ## self.n is the number of black edges. Remember this graph
        ## might not be a permutation
        self.n = 0
        for cycle in cycles :
            self.n = self.n + len(cycle)
        n = self.n
          
        # Creating nodes
        node_list = []
        node_list = [cycle_graph_node(i, False) for i in range(2*n)]
        self.begin_node = node_list[0 ]
        self.end_node   = node_list[-1]

        # Creating ap
        for i in range(0,2*n,2) :
            node_list[i  ].ap  = node_list[i+1]
            node_list[i+1].ap  = node_list[i  ]

        # Creating ab
        for i in range(1,2*n-1,2) :
            node_list[i  ].ab  = node_list[i+1]
            node_list[i+1].ab  = node_list[i  ]

        # Creating ac 
        for cycle in cycles :
            for i in range(len(cycle)) :               
                front, back  = -1,-1 # from left of the black edge.
                j = (i+1)%len(cycle)

                if cycle[i] > 0 :
                    front = 2*( cycle[i]  -1 )
                else :
                    front = 2*(-cycle[i]) -1

                if cycle[j] > 0 :
                    back = 2*( cycle[j]) -1
                else :
                    back = 2*(-cycle[j]  -1 )

                node_list[front].ac = node_list[back]
                node_list[back].ac  = node_list[front]


    def get_comps(self) :
        num_comp = 0
        
        
        twocycles = self.get_cycles()
        
        
        comps = []
                
        for cycle in twocycles :
            if len(cycle) > 1:
                maxcycle = max(cycle)
                mincycle = min(cycle)
                if mincycle < 0:
                    mincycle = -mincycle
                currComp = [mincycle, maxcycle, [cycle]]
                if len(comps) == 0:
                    comps.append(currComp)
                else :
                    i = 0
                    while i < len(comps):
                        ccycles = comps[i][2]
                        for compc in ccycles:
                            a1,a2 = max(cycle), min(cycle)
                            if a2 < 0:
                                a2 = -a2
                            b1,b2 = max(compc), min(compc)
                            if b2 < 0:
                                b2 = -b2
                                    
                            if b1 > a1 > b2 > a2 or a1 > b1 > a2 > b2:
                                compmin, compmax, toAppend = comps.pop(i)
                                currComp[2] = currComp[2] + toAppend
                                if compmin < currComp[0]:
                                    currComp[0] = compmin
                                if compmax > currComp[1]:
                                    currComp[1] = compmax
                                i = i - 1
                                break
                        i = i + 1
                    comps.append(currComp)
        
        
        i = 0
        while i < len(comps):
            if '-' in str(comps[i]):
                del comps[i]
                i = i - 1
            i = i + 1
            
        return comps

############################################################                
################ Rearrangement Operations  #################
############################################################                

            
    # The parameter original tells us if we want i,j,k to be the
    # indexing of the structure or the indexing of the structure befor
    # a shift or mirror operation.
    def transposition(self, i, j, k) :
        node_i = None
        node_j = None
        node_k = None

        unp_i, unp_j, unp_k = 0,0,0

        count     = 0
        unp_count = 0

        node = self.begin_node
        # Find the black edges
        while node :
            count = count + 1
            if not node.padded :
                unp_count = unp_count + 1

            if count == i :
                node_i = node
                unp_i  = unp_count
            if count == j :
                node_j = node
                unp_j  = unp_count
            if count == k :
                node_k = node
                unp_k  = unp_count
            node = node.ap.ab

        # Change the edges
        node_i.ap.ap = node_k
        node_j.ap.ap = node_i
        node_k.ap.ap = node_j

        aux       = node_i.ap
        node_i.ap = node_j.ap
        node_j.ap = node_k.ap
        node_k.ap = aux

        self.__num_cycles           = False
        self.__num_odd_cycles       = False
        self.reset_indices()
        return unp_i, unp_j, unp_k
        
    def reversal(self, i, j) :
        node_i = None
        node_j = None

        unp_i, unp_j = 0,0

        count     = 0
        unp_count = 0
        ## These variables are used to return the transposition
        ## applied as integer. ret_i, and ret_j will be the same
        ## as i,j if we do not have ignored black edges
        node = self.begin_node
        # Find the black edges

        while node :

            count = count + 1
            if not node.padded :
                unp_count = unp_count + 1

            if count == i :
                node_i = node
                unp_i  = unp_count
            if count == j+1 :
                node_j = node
                unp_j  = unp_count - 1
            node = node.ap.ab

        # Change the edges
        node_i.ap.ap = node_j.ap
        node_j.ap.ap = node_i.ap

        node_i.ap  = node_j
        node_j.ap  = node_i

        self.__num_cycles           = False
        self.__num_odd_cycles       = False
        self.reset_indices()
        return unp_i, unp_j

############################################################                
######################## Bounds  ###########################
############################################################                
    def upper_bound(self) :
        return self.n - self.num_cycles()

    def lower_bound(self) :
        return int(math.ceil( (self.n - self.num_odd_cycles())/2.0 ))

############################################################                
############## Cycle Graph Transformations  ################
############################################################                

#### HP Exact Signed Reversal Distance
#### Simple permutation with 1,2-cycles only

    def check_interleaving(self, b1, b2, c1, c2):
        d1, d2 = max(b1,b2), min(b1,b2)
        e1, e2 = max(c1,c2), min(c1,c2)

        if d1 > e1 > d2 > e2 or e1 > d1 > e2 > d2:
            return True
        return False

    def find_interleaving_another_cycle(self, cross1, node):
        vb = None
        wb = None
        wg = None
        vg = None

        curr = cross1.ap.ab
        while curr != node:
            if curr.ac.index < cross1.index or curr.ac.index > node.index:
                break
            curr = curr.ap
            if curr.ac.index < cross1.index or curr.ac.index > node.index:
                break
            curr = curr.ab
        #verifica se posso pegar uma aresta cinza a partir do ultimo
        if cross1.ap.ac.index < curr.index:
            wg = cross1.ap.ac
            vg = wg.ac
        #se nao puder, pega o ultimo como b
        else:
            vb = cross1.ap
            wb = vb.ap
        #verifica se posso pegar uma aresta cinza a partir do primeiro
        if wg == None and node.ap.ac.index > curr.index:
            wg = node.ap
            vg = wg.ac
        #se nao puder, pega o primeiro como b
        else:
            vb = node
            wb = node.ap
        
        return vb, wb, wg, vg

    def find_interleaving_same_cycle(self, node, b1, b2):
        #start = node
        prev = node.ap
        start = prev
        curr = prev.ac
            
        while curr != start:
            if self.check_interleaving(b1,b2,prev.index,curr.index):
                return [max(prev.index, curr.index), min(prev.index, curr.index)]
            prev = curr.ap
            curr = prev.ac
        return None # just in case...
        
    # return True plus the last black edge if is non oriented and convergent
    # and return False plus an oriented/divergent pair otherwise
    def is_non_oriented_convergent(self, node):
        start = node
        prev = node.ap
        # by definition, prev.index < start.index
        # let us continue to the third black edge
        curr = prev.ac

        while curr != start:
            if (curr.index > prev.index) or (curr.index % 2 == prev.index % 2):
                return(False, [max(curr.index, prev.index), min(curr.index, prev.index)])
            prev = curr.ap
            curr = prev.ac
        return(True, prev)
        
    def find_safe_split(self, node, cross1, cross2):
        vb = None
        wb = None
        wg = None
        vg = None

        start = node

        if start.index != cross1[0] and start.index != cross2[0]:
            wg = start.ac
            vg = start

        else:
            if start.ap.index != cross1[0] and start.ap.index != cross2[0]:
                wg = start.ap
                vg = start.ap.ac

        # if both gray edges cannot be used, let us use the black edge
        #    between them as vb and wb
        if not vg:
            vb = start
            wb = start.ap
            gray = wb.ac.ap
            wg = gray
            vg = gray.ac

        # if we alredy hae wg/vg, let us pick the first black edge in the path
        # after gray edge cross1 or cross2
        else:
            start2 = vg.ap
            while start2.index != cross1[0] and start2.index != cross1[1] and start2.index != cross2[0] and start2.index != cross2[1]:
                start2 = start2.ac.ap
            vb = start2.ac
            wb = vb.ap

        return vb, wb, wg, vg
              
    def transform_into_super_simple_permutation(self) :
        node = self.end_node                
        while node :
            
            b1  = node
            b2  = b1.ap.ac
            b3  = b2.ap.ac

            if b1 != b2 and b1 != b3 :
                isNon, cross1 = self.is_non_oriented_convergent(node)
                
                if isNon:
                    vb, wb, wg, vg = self.find_interleaving_another_cycle(cross1, node)
                
                else:
                    cross2 = self.find_interleaving_same_cycle(node, cross1[0], cross1[1])
                    vb, wb, wg, vg = self.find_safe_split(node, cross1, cross2) 

                ## The cycle has more than 2 black edges
                v = cycle_graph_node(None, True)
                w = cycle_graph_node(None, True)
                
                ## setting white edges
                w.ab = v
                v.ab = w
                
                ## setting black edges
                w.ap = wb
                v.ap = vb
                wb.ap = w
                vb.ap = v
                
                ## setting gray edges
                w.ac = wg
                v.ac = vg
                wg.ac = w
                vg.ac = v
                
                
                reset  = self.begin_node 
                count = 0

                while reset :
                    reset.index = count
                    reset       = reset.ap
            
                    count      = count + 1
            
                    reset.index = count
                    reset       = reset.ab
            
                    count      = count + 1

            else :
                node = node.ap.ab

        ## Fazer esse aqui
        self.__num_cycles           = False
        self.__num_odd_cycles       = False
        self.reset_indices()

        self.n = 0
        node = self.begin_node
        while node :
            self.n += 1
            node = node.ap.ab


    def transform_into_simple_permutation(self) :
        node = self.end_node                
        while node :
            b3 = node
            b1 = b3.ap.ac
            b2 = b1.ap.ac
            vg  = b2.ap.ac

            if b3 != b1 and b3 != b2 and b3 != vg :
                ## The cycle has more than 3 black edges
                v = cycle_graph_node(None, True)
                w = cycle_graph_node(None, True)

                ## Setting edges for v and w
                w.ab = v
                v.ab = w
                w.ap = b3.ap
                v.ap = b3
                w.ac = b2.ap
                v.ac = vg 

                #Setting other pointers
                b3.ap.ap = w
                b3.ap    = v
                b2.ap.ac = w
                vg.ac    = v
            else :
                node = node.ap.ab

        ## Fazer esse aqui
        self.__num_cycles           = False
        self.__num_odd_cycles       = False
        self.reset_indices()

        self.n = 0
        node = self.begin_node
        while node :
            self.n += 1
            node = node.ap.ab
        


############################################################                
################### Auxiliary Methods  #####################
############################################################                
    def print_indices(self) :
        node = self.begin_node

        while node :
            print("%i, padded = %s" % (node.index, node.padded))
            node = node.ap
            print("%i, padded = %s" % (node.index, node.padded))
            node = node.ab


    def get_cycles(self, want_vertices = False) :
        self.clean_visit()        

        node = self.end_node        
        cycles    = []
        vertices  = []

        while node :
            if not node.visit :
                cycle_node  = node
                cycle       = []
                cycle_nodes = []

                while not cycle_node.visit :
                    if cycle_node.index % 2 == 0 :
                        cycle.append( -(cycle_node.index+2)/2 )
                    else :
                        cycle.append( +(cycle_node.index+1)/2 )


                    cycle_node.visit = True
                    cycle_nodes.append(cycle_node)
                    cycle_node = cycle_node.ap
                    cycle_node.visit  = True
                    cycle_nodes.append(cycle_node)
                    cycle_node = cycle_node.ac
                    
                cycles.append(tuple(cycle))
                vertices.append(cycle_nodes)

            node = node.ap.ab
        if want_vertices :
            return tuple(cycles), vertices
        return tuple(cycles)

    def reset_indices(self) :
        node  = self.begin_node 
        count = 0

        while node :
            node.index = count
            node       = node.ap
            
            count      = count + 1
            
            node.index = count
            node       = node.ab
            
            count      = count + 1

    def num_cycles(self) :
        if type(self.__num_cycles) == bool :
            self.calculate_cycles()
        return self.__num_cycles

    def num_odd_cycles(self) :
        if type(self.__num_odd_cycles) == bool :
            self.calculate_cycles()
        return self.__num_odd_cycles


    def calculate_cycles(self) :
        cycles, vertices = self.get_cycles(want_vertices = True)
        num_cycles = len(cycles)
        num_odd = 0

        for cycle in cycles :
            if len(cycle) % 2 == 1 :
                num_odd = num_odd + 1

        self.__num_cycles           = num_cycles
        self.__num_odd_cycles       = num_odd

        for i in range(len(cycles)) :
            cycle = cycles[i]
            kind = 0
            if len(cycle) == 1 :
                kind = 1
            elif len(cycle) == 2 :
                if cycle[1] > 0 :
                    kind = 3
                else :
                    kind = 4
            elif len(cycle) == 3 :
                if cycle[1] > 0 and cycle[2] > 0 :
                    if cycle[2] > cycle[1] :
                        kind = 2
                    else :
                        kind = 5
                elif cycle[1] < 0 and cycle[2] < 0 :
                    if cycle[2] > cycle[1] :
                        kind = 6
                    else :
                        kind = 7
                else :
                    if abs(cycle[2]) > abs(cycle[1]) :
                        kind = 6
                    else :
                        kind = 7

            vertice_set = vertices[i]
            for vertex in vertice_set :
                vertex.kind  = kind
                vertex.cycle = i

    def clean_visit(self) :
        node = self.begin_node
        
        while node :
            node.visit = False
            node       = node.ap
            node.visit = False
            node       = node.ab

        
#####################################################################
################## REPRESENTS A NODE OF A GRAPH #####################
#####################################################################

def construct_str_cycle(permutationstr) :
        permutation = eval("[%s]" % permutationstr) 

	n = len(permutation)

	permutation = [0] + permutation + [n+1]
	position    = [-1 for i in range(0, n+2)]
	#sign        = [-1 for i in range(0, n+2)]


	for i in range(1, n+2) :
	    position[abs(permutation[i])] = i
	#    sign    [abs(permutation[i])] = permutation[i] / abs(permutation[i])

	## 1 if the gray edge i,-(i+1) was never used.
	gray_available     = [1 for i in range(0, n+1)]
	#black_available    = [1 for i in range(0, n+1)]

	cycles = []

	for i in range(0, n+1) :

	    ## 
		if gray_available[i] :

			start = i
			cycle = [start]

			end   = start
			positive  = True
		
			while True :
		    
			    ## Will be used later, it says if after walking through
			    ## the black edge we are in the right or in the left
			    is_vertex_left = None

			    if positive :
			        ## Gray edge: we are looking for the edge ( end,-(end+1) )
			        gray_available[end] = gray_available[end] - 1
			        end = end + 1
			        cycle.append(end)

			        ## Black edge: we are at the vertex -end.
			        if permutation[position[end]] > 0 :
			            # If the sign in that position is positive, than
			            # -end is in the left (cycle graph)                    
			            end = abs(permutation[position[end]-1])
			            is_vertex_left = False
			        
			        else :
			            # If the sign in that position is negative, than
			            # -end is in the right (cycle graph)
			            end = abs(permutation[position[end]+1])
			            is_vertex_left = True
			    else :
			        ## Gray edge: we are looking for the edge ( -end, end-1  )
			        end = end - 1                                 ##  Note we swapped
			        gray_available[end] = gray_available[end] - 1 ##  these lines
			        cycle.append(end)

			        ## Black edge: we are at the vertex +end.
			        if permutation[position[end]] > 0 :
			            # If the sign in that position is positive, than
			            # +end is in the right (cycle graph)
			            end = abs(permutation[position[end]+1])
			            is_vertex_left = True
			        else : 
			            # If the sign in that position is negative, than
			            # +end is in the left (cycle graph)
			            end = abs(permutation[position[end]-1])
			            is_vertex_left = False
			            
			    if end == start :
			        break
			    else :
			        cycle.append(end)
			        
			        if is_vertex_left :
			            if permutation[position[end]] < 0 :
			                positive = True
			            else :
			                positive = False
			        else :                    
			            if permutation[position[end]] < 0 :
			                positive = False
			            else :
			                positive = True
			cycles.append(cycle)

        return cycles


class cycle_graph_node :
    #index  : stores the black edge i, 0 <= i <= n+1
    #ap     : points to the record that stores pi_{i-1}, 1 <= i <= n+1
    #ab     : points to the record that stores pi_{i+1}, 0 <= i <= n
    #ac     : points to the record that stores i + 1,    0 <= i <= n
    #rac    : reverse of the ac
    #visit  : indicates if the record has been visited
    #cend   : stores the black edge i_k in the canonical representation
    def __init__(self, index, padded) :
        self.index    = index
        self.padded   = padded
        self.cycle    = 0 ## Which cycle the node belongs to
        self.pcycle   = 0 ## The node position in the cycle.

        ## Kind:
        ## 0 = unset
        ## 1 = small cycle             (1)
        ## 2 = oriented    convergent  (3, 1, 2)
        ## 3 = even        convergent  (2,  1)
        ## 4 = even        divergent   (2, -1)
        ## 5 = nonoriented convergent  (3, 2, 1)
        ## 6 = oriented    divergent   (3,-2,-1), (3,1,-2), (3,-1, 2)
        ## 7 = nonoriened  divergent   (3,2,-1),  (3,-2,1), (3,-1,-2)
        self.kind     = 0
        self.ap, self.ab, self.ac = 0,0,0
        self.visit  = False

if __name__ == '__main__':
    ## a simply 'how to'
    if sys.argv[1] == '-h' or len(sys.argv) != 3 :
        print ('Input:')
        print ('  python sbsrtwpr.py <permutation> <frac>')
        print ('    -permutation     = a comma-separated signed permutation')
        print ('    -frac            = the desired proportion between reversals and transpositions (between 0 and 1)')
        print ('Output:')
        print ('  <len(operations)> <operations> <prop>')
        print ('    -operations = a sorting sequence for the input permutation (respecting the proportion) ')
        print ('    -prop       = (number of reversals in <operations>) / len(operations) ')


    else:
        str_permutation = sys.argv[1]
        frac = float(sys.argv[2])

        permutation = eval("[%s]" % str_permutation)
        n = len(permutation)        
        permutation = [0] + permutation + [n+1]

        position    = get_position(permutation)
        cycles = construct_str_cycle(str_permutation) 
        
        config = canonical_representation(cycles, position)

        sort = heuristic_sort_dias2015(config)
        sort.sort(permutation, frac)

