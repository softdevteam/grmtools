searchState.loadedDescShard("lrtable", 0, "A type specifically for state table indices.\nHow many edges does this <code>StateGraph</code> contain?\nHow many states does this <code>StateGraph</code> contain? NB: By …\nReturn the itemset for closed state <code>stidx</code>. Panics if <code>stidx</code> …\nReturn the itemset for core state <code>stidx</code> or <code>None</code> if it doesn…\nReturn the state pointed to by <code>sym</code> from <code>stidx</code> or <code>None</code> …\nReturn the edges for state <code>stidx</code>. Panics if <code>stidx</code> doesn’…\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nReturn an iterator over all closed states in this …\nReturn an iterator over all core states in this <code>StateGraph</code>.\nReturn an iterator which produces (in order from …\nPretty print this stategraph as a <code>String</code>. If <code>core_states</code> …\nReturn a pretty printed version of the closed states, and …\nReturn a pretty printed version of the core states, and …\nReturn this state graph’s start state.\nAccept this input.\nNo valid action.\nReduce production X in the grammar.\nShift to state X in the statetable.\nA representation of a <code>StateTable</code> for a grammar. <code>actions</code> …\nAny error from the Yacc parser returns an instance of this …\nThe various different possible Yacc parser errors.\nReturn the action for <code>stidx</code> and <code>sym</code>, or <code>None</code> if there isn…\nReturn a struct containing all conflicts or <code>None</code> if there …\nReturn an iterator over a set of “core” reduces of …\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturn the goto state for <code>stidx</code> and <code>ridx</code>, or <code>None</code> if there …\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nReturns a pretty-printed version of the conflicts.\nReturns a pretty-printed version of the reduce/reduce …\nReturns a pretty-printed version of the shift/reduce …\nDoes the state <code>stidx</code> 1) only contain reduce (and error) …\nReturn an iterator over all reduce/reduce conflicts.\nHow many reduce/reduce conflicts are there?\nReturn an iterator over all shift/reduce conflicts.\nHow many shift/reduce conflicts are there?\nReturn this state table’s start state.\nReturn an iterator over the indexes of all non-empty …\nReturn an iterator over the indexes of all shift actions …")