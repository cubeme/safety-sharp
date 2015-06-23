echo start nusmv > nusmv_start
nusmv ffb.smv > result_nusmv.txt
echo end nusmv > nusmv_end

echo start nuxmv > nuxmv_start
nuxmv ffb.smv > result_nusmv.txt
echo end nuxmv > nuxmv_end

echo start nusmv > nusmv_coi_start
nusmv -coi ffb.smv > result_nusmv_coi.txt
echo end nusmv > nusmv_coi_end