export function getUserDetails() {
	const cookie = document.cookie.split(';').find((c) => c.trim().startsWith('authorization_token='));
	const token = cookie.replace('authorization_token=', '');
	const base64Url = token.split('.')[1];
	const base64 = base64Url.replace(/-/g, '+').replace(/_/g, '/');
	const jsonPayload = decodeURIComponent(
		atob(base64)
			.split('')
			.map((c) => '%' + ('00' + c.charCodeAt(0).toString(16)).slice(-2))
			.join('')
	);

	const json = JSON.parse(jsonPayload);
	return { "user_type": json.user_type, "user_id": json.user_id };
}