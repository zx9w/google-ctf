module NetCat

where

import System.Process

cmdstr :: String
cmdstr = "nc reality.ctfcompetition.com 1337"

nc :: CmdSpec
nc = ShellCommand cmdstr

cmd :: CreateProcess -- CmdSpec cwd env stdin stdout stderr fds some other things
cmd = CreateProcess (nc Nothing Nothing NoStream CreatePipe NoStream False False False False False False Nothing Nothing False)

-- The idea is to spawn the process
-- then cleanupProcess once we have gotten the third datapoint

-- (putStr . show) =<< (createProcess cmd)
