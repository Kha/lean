/- projections such as `bind` should _not_ be unfolded here just
   because they contain a universe mvar -/
instance : is_lawful_monad list := {}
