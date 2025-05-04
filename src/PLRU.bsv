export PLRU;
export choose;
export next;
export Tree(..);
export toTree;
export fromTree;

// BCache is not happy with TSub#(ways,1), I dont' know why
typedef Bit#(ways) PLRU#(numeric type ways);

typedef union tagged {
  void Leaf;
  struct {
    Bit#(1) dir;
    Tree lhs;
    Tree rhs;
  } Node;
} Tree deriving(FShow, Eq);

function Tree toTree(PLRU#(ways) plru);
  function Tree doRec(Integer pos, Integer size);
    if (size == 1) return Leaf;
    else begin
      Bit#(1) dir = plru[pos];

      Integer half = size / 2;
      Tree lhs = doRec(pos+1, half);
      Tree rhs = doRec(pos+half, size-half);

      return tagged Node {dir: dir, lhs: lhs, rhs: rhs};
    end
  endfunction


  return doRec(0, valueOf(ways));
endfunction

function PLRU#(ways) fromTree(Tree tree);
  function PLRU#(ways) doRec(Tree t, Integer size);
    Integer half = size / 2;

    case (t) matches
      Leaf : return 0;
      tagged Node{dir: .dir, lhs: .lhs, rhs: .rhs} : begin

        PLRU#(ways) l = doRec(lhs, half) << 1;
        PLRU#(ways) r = doRec(rhs, half) << half;

        return (dir == 1 ? 1 : 0) | l | r;
      end
    endcase
  endfunction

  return doRec(tree, valueOf(ways));
endfunction

function Bit#(a) chooseTree(Tree tree, Integer size);
  Integer half = size / 2;

  case (tree) matches
    Leaf : return 0;
    tagged Node{dir: .dir, lhs: .lhs, rhs: .rhs} : begin
      return dir == 1 ?
        1 + (chooseTree(lhs, half) << 1) :
        (chooseTree(rhs, half) << 1);
    end
  endcase
endfunction

function Bit#(TLog#(ways)) choose(PLRU#(ways) plru);
  return chooseTree(toTree(plru), valueOf(ways));
endfunction

function Tree nextTree(Tree tree, Bit#(a) path, Integer size);
    Integer half = size / 2;

    case (tree) matches
      Leaf : return Leaf;
      tagged Node{dir: .dir, lhs: .lhs, rhs: .rhs} : begin
        return tagged Node{
          dir: ~path[0],
          lhs: path[0] == 1 ? nextTree(lhs, path >> 1, half) : lhs,
          rhs: path[0] == 0 ? nextTree(rhs, path >> 1, half) : rhs
        };
      end
    endcase
endfunction

function PLRU#(ways) next(PLRU#(ways) plru, Bit#(TLog#(ways)) path);
  return fromTree(nextTree(toTree(plru), path, valueOf(ways)));
endfunction
