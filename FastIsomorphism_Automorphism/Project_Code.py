from graph import *
import graph_io
from graph_io import *
from basicpermutationgroup import *

FILEPATH = ""

queue = []

def init_color(graph):
    graph.colors = [0] * len(graph.vertices)

def start_refinement(graphs, vertices_graph1, vertices_graph2):
    global queue
    queue = []
    queue.append(0)
    init_color(graphs[1])
    init_color(graphs[0])
    vertices_combined = []
    coloring = []
    coloring.append(0)
    for vertex in graphs[0].vertices:
        if vertex not in vertices_graph1:
            vertex.color = 0
            vertex.colornum = 0
        else:
            vertex.color = vertices_graph1.index(vertex) + 1
            vertex.colornum = vertices_graph1.index(vertex) + 1
            queue.append(vertices_graph1.index(vertex) + 1)
            coloring.append(vertices_graph1.index(vertex) + 1)
        vertices_combined.append(vertex)
    for vertex in graphs[1].vertices:
        if vertex not in vertices_graph2:
            vertex.colornum = 0
            vertex.color = 0
        else:
            vertex.color = vertices_graph2.index(vertex) + 1
            vertex.colornum = vertices_graph2.index(vertex) + 1
        vertices_combined.append(vertex)

    color_class = 0
    while len(queue) != 0 and color_class != None:
        color_class, coloring = refine(vertices_combined, color_class, coloring)

    for vertex in graphs[0]:
        graphs[0].colors[vertex.label] = vertex.color
    for vertex in graphs[1]:
        graphs[1].colors[vertex.label] = vertex.color

def is_discrete(graph):
    return len(set(graph.colors)) == len(graph.vertices)

def get_vertices_of_color_class(graph, color_class):
    return [index for index, color in enumerate(graph.colors) if color == color_class]

def get_vertices_of_color_class_in_list(color_list, color_class):
    return [vertex for vertex in color_list if vertex.color == color_class]

def neighbour_same_color(vertex, color):
    count = 0
    for neighbour in vertex.neighbours:
        if neighbour.color == color:
            count += 1
    return count

def refine(graphs, color_class, coloring):
    global queue
    new_coloring = {vertex:vertex.color for vertex in graphs}
    for color in coloring:
        neighbour_color_count = dict()
        neighbourhood = get_vertices_of_color_class_in_list(graphs, color)
        if len(neighbourhood) > 1:
            for vertex in neighbourhood:
                neighbour_color_count[vertex] = neighbour_same_color(vertex, color_class)
            set_of_color = set(neighbour_color_count.values())
            if len(set_of_color) > 1:
                already_checked = dict()
                for key_vertex in neighbour_color_count.keys():
                    if neighbour_color_count[key_vertex] != min(set_of_color):
                        if neighbour_color_count[key_vertex] not in already_checked:
                            new_color = max(set(new_coloring.values())) + 1
                            already_checked[neighbour_color_count[key_vertex]] = new_color
                            new_coloring[key_vertex] = new_color
                            if new_color not in queue:
                                queue.append(new_color)
                        else:
                            new_coloring[key_vertex] = already_checked[neighbour_color_count[key_vertex]]
    queue.remove(color_class)
    for vertex in graphs:
        if new_coloring[vertex] != vertex.color:
            vertex.color = new_coloring[vertex]
            vertex.colornum = new_coloring[vertex]
    minimum = float('inf')
    new_color = None
    for color in set(new_coloring.values()):
        if color in queue:
            count = get_vertices_of_color_class_in_list(graphs, color)
            if len(count) < minimum:
                new_color = color
                minimum = len(count)
    return new_color, list(set(new_coloring.values()))

def get_vertices_of_color(graph1, graph2, col):
    res = []
    for v1 in graph1.vertices:
        if graph1.colors[v1.label] == col:
            res.append(v1)
    for v2 in graph2.vertices:
        if graph2.colors[v2.label] == col:
            res.append(v2)
    return res

def create_sets(graph):
    graph2 = Graph(False, len(graph.vertices))
    for edge in graph.edges:
        va = graph2.vertices[edge.head.label]
        vb = graph2.vertices[edge.tail.label]
        graph2.add_edge(Edge(va, vb))
    return check_automorphism(graph, graph2, [], [], [], True)

def check_automorphism(graph1, graph2, vert1, vert2, generating_set, trivial):

    new_vert1 = vert1[:len(vert2)]
    start_refinement([graph1, graph2], new_vert1, vert2)

    if not is_balanced([graph1, graph2]):
        return generating_set

    if is_bijection([graph1, graph2]):
        perm = find_permutation(graph1, graph2)
        generating_set.append(permutation(len(graph1.vertices), mapping=perm))
        return generating_set

    color = select_partitioning_color(graph1)
    starting_vertex = get_starting_vertex(graph1, graph2, color)

    if starting_vertex not in vert1:
        vert1.append(starting_vertex)

    return handle_recursion(graph1, graph2, vert1, vert2, generating_set, trivial, starting_vertex, color)


def find_permutation(graph1, graph2):
    perm = [0] * len(graph1.vertices)
    for vertex_index in range(len(graph1.colors)):
        vertices = get_vertices_of_color(graph1, graph2, graph1.colors[vertex_index])
        first_vertex = vertices[0] if vertices[0] in graph1.vertices else vertices[1]
        second_vertex = vertices[1] if first_vertex == vertices[0] else vertices[0]

        perm[first_vertex.label] = second_vertex.label

    return perm

def select_partitioning_color(graph1):
    color = None
    min_count = float('inf')
    for c in set(graph1.colors):
        count = graph1.colors.count(c)
        if count < min_count and count >= 2:
            min_count = count
            color = c
    return color


def get_starting_vertex(graph1, graph2, color):
    for vertex in get_vertices_of_color(graph1, graph2, color):
        if vertex in graph1.vertices:
            return vertex
    return None


def handle_recursion(graph1, graph2, vert1, vert2, generating_set, trivial, starting_vertex, color):

    same_color_vertices = get_vertices_of_color(graph1, graph2, color)
    new_list = [v for v in same_color_vertices if v in graph2.vertices]
    
    possible_vert2 = vert2.copy()
    counter = 0

    while counter < len(new_list):
        for vertex in possible_vert2:
            if vertex in new_list:
                possible_vert2.remove(vertex)
        possible_vert2.append(new_list[counter])
        is_trivial = starting_vertex.label == new_list[counter].label

        generating_set = check_automorphism(graph1, graph2, vert1, possible_vert2, generating_set, is_trivial)

        if not trivial:
            return generating_set
        
        counter += 1

    return generating_set

def is_balanced(graphs):
    return sorted(graphs[0].colors.copy()) == sorted(graphs[1].colors.copy())

def is_bijection(graphs):
    g1 = graphs[0]
    g2 = graphs[1]
    l1 = []
    l2 = []
    s1 = set()
    s2 = set()
    for i in range(len(g1.colors)):
        l1.append(g1.colors[i])
        s1.add(g1.colors[i])
    for i in range(len(g2.colors)):
        l2.append(g2.colors[i])
        s2.add(g2.colors[i])
    l1.sort()
    l2.sort()
    s1 = sorted(s1)
    s2 = sorted(s2)
    if l1 != l2:
        return False
    if list(s1) == l1 and list(s2) == l2:
        return True
    return False

def calc_orb_stab(gs, vtx):
    the_orb = Orbit(gs, vtx)
    stab = Stabilizer(gs, vtx)
    return the_orb, stab


def compute_answer(orb, stab, graph):
    stab_auto = get_automorphisms(stab, graph)
    correct_ans = len(orb)*stab_auto
    return correct_ans


def get_automorphisms(gs, graph):
    if not gs:
        return 1
    le = len(graph.vertices)
    for x in range(le):
        o, s = calc_orb_stab(gs, x)
        if len(o) > 1:
            return compute_answer(o, s, graph)

def check_isomorphism(graph1, graph2, vert1, vert2):
    new_vert1 = vert1[:len(vert2)]
    start_refinement([graph1, graph2], new_vert1, vert2)
    if not is_balanced([graph1, graph2]):
        return False
    elif is_bijection([graph1,graph2]):
        return True
    color = None
    vertex_graph1 = None
    possible_color_min = float('inf')
    for new_color in set(graph1.colors):
        counted_color = list(graph1.colors).count(new_color)
        if counted_color < possible_color_min and counted_color > 1:
            color = new_color
            possible_color_min = counted_color
    new_vertices = []
    for vertex in get_vertices_of_color(graph1, graph2, color):
        if vertex in graph1 and vertex_graph1 == None and vertex not in vert1:
            vertex_graph1 = vertex
            continue
        if vertex in graph2:
            new_vertices.append(vertex)
            continue
    new_vert1.append(vertex_graph1)
    for vertex in new_vertices:
        possible_vertices = vert2[:]
        possible_vertices.append(vertex)
        if check_isomorphism(graph1, graph2, new_vert1, possible_vertices):
            return True
        else:
            continue
    return False

if __name__ == '__main__':
        with open(FILEPATH, 'r') as file:
            graphs = graph_io.load_graph(file, Graph, True)[0]
            results = []
            done = []
            sets_list = []
            for index in range(len(graphs)):
                graph = graphs[index]
                if graphs.index(graph) not in done:
                    if "Aut" in FILEPATH:
                        sets = create_sets(graph)
                        automorph = get_automorphisms(sets, len(graph.vertices))
                    solution = [graphs.index(graph)]
                    if "GI" in FILEPATH:
                        for compare_index in range(index + 1, len(graphs)):
                            compare_graph = graphs[compare_index]
                            if compare_graph not in done:
                                if check_isomorphism(graph, compare_graph,[],[]):
                                    done.append(graphs.index(compare_graph))
                                    solution.append(graphs.index(compare_graph))
                        if "Aut" in FILEPATH:
                            results.append((solution, automorph))
                        else:
                            results.append(solution)
                    else:
                        results.append((solution, automorph))
            print("\n" + FILEPATH)
            if "Aut" in FILEPATH:
                for result in results:
                    print(str(result[0]) + ": " + str(result[1]))
            else:
                for result in results:
                    print(result)