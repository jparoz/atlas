use tree_sitter::Tree;

#[derive(Debug, Clone)]
pub struct LuaFile {
    pub tree: Tree,
    pub src: String,
}

impl LuaFile {
    pub fn new(tree: Tree, src: String) -> Self {
        LuaFile { tree, src }
    }
}
