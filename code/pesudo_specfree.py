
# suppose we defined the get_neighbors(node, taxiway) the nodes on a certain taxiway
# suppose we have a function last_node(node_list) to return the last element
# suppose we have a function drop_last(node_list) to return the list without last element
# suppose we have a function node_find(node, nodelist) to return whether a node is in a nodelist, it can acceptu for nil list
# is_on_taxiway(node, taxiway) return bool
taxiway := list of edge = list of (node, node)
(A,B) (B,A)
get_neighbors = search key=node in taxiway
#============================= get_last_segment======================
    


# this function is to search all the neighbors except for the previous node
def last_segment(pre_node_list, cur_node, aim_node, taxiway, neighbors):   

    if cur_node in pre_node_list:   # it is a loop
        return []

    if neighbors = []:
        return []
    else if head(neighbors) == aim_node:    # finally we get the right path
        return cur_node :: last_node(pre_node_list)

    # above are all cases that we have to return, including reach endpoint, no way to deeper, or loop

    else:   # this is not the case to return, we need to deeper or check other neighbors
        result = last_segment(cur_node::pre_node_list, head(neighbors), aim_node, taxiway, get_neighbors(head(neighbors), taxiway))
        if last_node(result) == last_node(pre_node_list): # the correct result
            return cur_node :: result   #pass on
        else: # include the case of back forward, result=[]
            return last_segment(pre_node_list, cur_node, aim_node, taxiway, tail(neighbors))



def get_last_segment(source_node, aim_node, taxiway):
    # we will at least have two nodes: source_node attached first, and source_node as a checker
    return tail(drop_last(last_segment([], source_node, aim_node, taxiway, get_neighbors(source_node, taxiway))))


#=============================== get_intermediate_nodes ===============

def intermediate_nodes(pre_node_list, cur_node, cur_taxi, next_taxi, neighbors):
    if cur_node in pre_node_list:
        return []
    
    if neighbors = []:
        return []
    else if is_on_taxiway(head(neighbors), next_taxi) == True:
        return cur_node :: last_node(pre_node_list)
    
    else:
        result = intermediate_nodes(cur_node::pre_node_list, head(neighbors), cur_taxi, next_taxi, get_neighbors(head(neighbors), cur_taxi))
        if last_node(result) == last_node(pre_node_list):
            return cur_node :: result
        else:
            return intermediate_nodes(pre_node_list, cur_node, cur_taxi, next_taxi, tail(neighbors))


def get_last_segment(source_node, cur_taxi, next_taxi):
    return tail(drop_last(intermediate_nodes([], source_node, cur_taxi, next_taxi, get_neighbors(source_node, cur_taxi))))

