module Data.LiveFusion.Backend where


class Code code where
  getNative :: code t -> t
