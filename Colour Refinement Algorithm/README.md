# Graph Color Refinement and Disjoint Set Analysis

This Python script performs color refinement on a list of graphs and identifies isomorphic graphs, including discrete graphs (graphs where all vertices have different colors). It uses a custom graph library (`graph` and `graph_io`) to load and process graph data.

## Prerequisites

- Python 3.x
- Custom graph library modules:
  - `graph.py`
  - `graph_io.py`

## Input

The script reads graph data from files starting with repair such as `repair4.grl` in a specific graph list format supported by the `graph_io` module.

## Functionality

1. **Graph Loading**
   - Loads a list of graphs from one of the repair grl files using `load_graph` with list reading enabled
   - Extracts individual graphs and vertices into separate lists

2. **Color Refinement (`col_ref` function)**
   - Implements an iterative color refinement algorithm
   - Assigns colors to vertices based on their neighborhood patterns
   - Continues until no further refinement is possible

3. **Key Features**
   - Tracks previous and new color assignments
   - Identifies isomorphic graphs by comparing color patterns
   - Detects discrete graphs (single-vertex graphs)
   - Maintains iteration count and refinement history

4. **Output**
   - Prints:
     - Groups of isomorphic graphs with their refinement iteration count
     - Whether each group represents discrete graphs
     - Final result as a list of tuples containing:
       - Vertex groups
       - Refinement iteration number
       - Discrete status flag
   - Shows total number of iterations

## Usage

1. Ensure the grl file you want is in the working directory
2. Place required `graph` and `graph_io` modules in the same directory
3. Run the script:
python Project_Code.py