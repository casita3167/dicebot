# 在處理 .rts 的區塊內，先檢查 list
if content == 'list':
    if tables:
        embed = discord.Embed(title="📋 已建立的抽籤表", color=0x00aaff)
        desc = ""
        for idx, (name, items) in enumerate(tables.items(), 1):
            desc += f"{idx}. **{name}** ({len(items)} 項)\n"
        embed.description = desc
        embed.set_footer(text=message.author.display_name, icon_url=message.author.display_avatar.url)
        await message.channel.send(embed=embed)
    else:
        await message.channel.send("📭 目前沒有任何抽籤表，使用 `.rts 名稱：項目1,項目2,...` 建立。")
    return True