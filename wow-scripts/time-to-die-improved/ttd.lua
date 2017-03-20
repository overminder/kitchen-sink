function()
	local N = 80

	WA_healthrate_time = WA_healthrate_time or 0
	WA_healthrate_index = WA_healthrate_index or 0
	WA_healthrate_pct = WA_healthrate_pct or {}
	WA_healthrate_n = WA_healthrate_n or 0

	local tar = UnitGUID("target")

  -- Reset.
	if (not tar) or tar ~= WA_healthrate_lasttar then
		WA_healthrate_time = GetTime()
		WA_healthrate_index = 0
		WA_healthrate_n = 0
	end

	if tar and GetTime() >= WA_healthrate_time then
		local pct = UnitHealth("target")/UnitHealthMax("target")*100

		WA_healthrate_index = (WA_healthrate_index+1)%N
		WA_healthrate_n = min(WA_healthrate_n+1, N)
		WA_healthrate_pct[WA_healthrate_index] = pct

		if WA_healthrate_lasttar == tar then
			local sumxy = 0
			local sumxx = 0
			local sumx = 0
			local sumy = 0
			for i=1,WA_healthrate_n do
				sumx = sumx + i
				sumxx = sumxx + i*i
				local y = WA_healthrate_pct[(WA_healthrate_index-WA_healthrate_n+i)%N]
				sumy = sumy + y
				sumxy = sumxy + i*y
			end
			WA_healthrate = (sumxy-(1/WA_healthrate_n)*sumx*sumy)/(sumxx-(1/WA_healthrate_n)*sumx*sumx)
			WA_healthrate_ttd = -pct/WA_healthrate
		else
			WA_healthrate = nil
		end

		WA_healthrate_time = GetTime() + 1
		WA_healthrate_lasttar = tar
	end

	if tar == WA_healthrate_lasttar and UnitCanAttack("player","target") then
		return true
	end
end
