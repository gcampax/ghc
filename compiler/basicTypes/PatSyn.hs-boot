module PatSyn where
import Name( NamedThing )
import Data.Typeable ( Typeable )
import Data.Data ( Data )
import Outputable ( Outputable, OutputableBndr )
import Unique ( Uniquable )

data PatSyn

instance Eq PatSyn
instance Ord PatSyn
instance NamedThing PatSyn
instance Outputable PatSyn
instance OutputableBndr PatSyn
instance Uniquable PatSyn
instance Typeable PatSyn
instance Data PatSyn
